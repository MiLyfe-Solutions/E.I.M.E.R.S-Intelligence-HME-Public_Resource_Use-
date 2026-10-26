import V185TrunkScan23Chunk0069

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_416076 : List Nat := [2, 2, 1, 3, 2, 1, 2, 10]
def baseStart_416076 : Nat := 118140960795 + 416076 * 2 ^ 59
def prefixEnd_416076 : Nat := 4983230072969 + 3 ^ 40 * 416076 * 2
def baseEnd_416076 : Nat := 7912850992600716090241

theorem tailTrace_416076 : CollatzResearch.WordTrace tailWord_416076 prefixEnd_416076 7912850992600716090241 := by
  unfold tailWord_416076
  simp only [CollatzResearch.WordTrace]
  refine ⟨7587769220317593484262041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10117025627090124645682721 7587769220317593484262041)
  ·
    refine ⟨5690826915238195113196531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7587769220317593484262041 5690826915238195113196531)
    ·
      refine ⟨8536240372857292669794797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5690826915238195113196531 8536240372857292669794797)
      ·
        refine ⟨3201090139821484751173049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8536240372857292669794797 3201090139821484751173049)
        ·
          refine ⟨2400817604866113563379787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3201090139821484751173049 2400817604866113563379787)
          ·
            refine ⟨3601226407299170345069681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2400817604866113563379787 3601226407299170345069681)
            ·
              refine ⟨2700919805474377758802261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3601226407299170345069681 2700919805474377758802261)
              ·
                refine ⟨7912850992600716090241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2700919805474377758802261 7912850992600716090241)
                ·
                  rfl

theorem cell23_416076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 10].length) (baseStart_416076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_416076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_416076 prefixEnd_416076 := by exact prefixLift 416076
  have htrace : WordTrace (prefixWord ++ tailWord_416076) baseStart_416076 baseEnd_416076 := by
    simpa [prefixWord, tailWord_416076, baseEnd_416076] using wordTrace_append hprefix tailTrace_416076
  have hstable : (prefixWord ++ tailWord_416076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416076).length < 2 ^ (prefixWord ++ tailWord_416076).sum := by decide
  have hdescent : baseEnd_416076 < baseStart_416076 := by decide
  rcases family_descends (prefixWord ++ tailWord_416076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416137 : List Nat := [1, 2, 1, 1, 6, 2, 1, 3, 2, 1, 3]
def baseStart_416137 : Nat := 118140960795 + 416137 * 2 ^ 59
def prefixEnd_416137 : Nat := 4983230072969 + 3 ^ 40 * 416137 * 2
def baseEnd_416137 : Nat := 213678299120143595773727

theorem tailTrace_416137 : CollatzResearch.WordTrace tailWord_416137 prefixEnd_416137 213678299120143595773727 := by
  unfold tailWord_416137
  simp only [CollatzResearch.WordTrace]
  refine ⟨15177763293414194386494665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10118508862276129590996443 15177763293414194386494665)
  ·
    refine ⟨11383322470060645789870999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15177763293414194386494665 11383322470060645789870999)
    ·
      refine ⟨17074983705090968684806499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11383322470060645789870999 17074983705090968684806499)
      ·
        refine ⟨25612475557636453027209749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17074983705090968684806499 25612475557636453027209749)
        ·
          refine ⟨1200584791764208735650457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25612475557636453027209749 1200584791764208735650457)
          ·
            refine ⟨900438593823156551737843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1200584791764208735650457 900438593823156551737843)
            ·
              refine ⟨1350657890734734827606765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 900438593823156551737843 1350657890734734827606765)
              ·
                refine ⟨506496709025525560352537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1350657890734734827606765 506496709025525560352537)
                ·
                  refine ⟨379872531769144170264403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 506496709025525560352537 379872531769144170264403)
                  ·
                    refine ⟨569808797653716255396605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 379872531769144170264403 569808797653716255396605)
                    ·
                      refine ⟨213678299120143595773727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 569808797653716255396605 213678299120143595773727)
                      ·
                        rfl

theorem cell23_416137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 2, 1, 3].length) (baseStart_416137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_416137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_416137 prefixEnd_416137 := by exact prefixLift 416137
  have htrace : WordTrace (prefixWord ++ tailWord_416137) baseStart_416137 baseEnd_416137 := by
    simpa [prefixWord, tailWord_416137, baseEnd_416137] using wordTrace_append hprefix tailTrace_416137
  have hstable : (prefixWord ++ tailWord_416137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416137).length < 2 ^ (prefixWord ++ tailWord_416137).sum := by decide
  have hdescent : baseEnd_416137 < baseStart_416137 := by decide
  rcases family_descends (prefixWord ++ tailWord_416137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416160 : List Nat := [2, 1, 1, 4, 1, 3, 1, 1, 3, 4, 2]
def baseStart_416160 : Nat := 118140960795 + 416160 * 2 ^ 59
def prefixEnd_416160 : Nat := 4983230072969 + 3 ^ 40 * 416160 * 2
def baseEnd_416160 : Nat := 213690109175197005786121

theorem tailTrace_416160 : CollatzResearch.WordTrace tailWord_416160 prefixEnd_416160 213690109175197005786121 := by
  unfold tailWord_416160
  simp only [CollatzResearch.WordTrace]
  refine ⟨7589301086165434657290967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10119068114887246209721289 7589301086165434657290967)
  ·
    refine ⟨11383951629248151985936451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7589301086165434657290967 11383951629248151985936451)
    ·
      refine ⟨17075927443872227978904677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11383951629248151985936451 17075927443872227978904677)
      ·
        refine ⟨3201736395726042746044627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17075927443872227978904677 3201736395726042746044627)
        ·
          refine ⟨4802604593589064119066941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3201736395726042746044627 4802604593589064119066941)
          ·
            refine ⟨1800976722595899044650103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4802604593589064119066941 1800976722595899044650103)
            ·
              refine ⟨2701465083893848566975155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1800976722595899044650103 2701465083893848566975155)
              ·
                refine ⟨4052197625840772850462733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2701465083893848566975155 4052197625840772850462733)
                ·
                  refine ⟨1519574109690289818923525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4052197625840772850462733 1519574109690289818923525)
                  ·
                    refine ⟨284920145566929341048161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1519574109690289818923525 284920145566929341048161)
                    ·
                      refine ⟨213690109175197005786121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 284920145566929341048161 213690109175197005786121)
                      ·
                        rfl

theorem cell23_416160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_416160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_416160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_416160 prefixEnd_416160 := by exact prefixLift 416160
  have htrace : WordTrace (prefixWord ++ tailWord_416160) baseStart_416160 baseEnd_416160 := by
    simpa [prefixWord, tailWord_416160, baseEnd_416160] using wordTrace_append hprefix tailTrace_416160
  have hstable : (prefixWord ++ tailWord_416160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416160).length < 2 ^ (prefixWord ++ tailWord_416160).sum := by decide
  have hdescent : baseEnd_416160 < baseStart_416160 := by decide
  rcases family_descends (prefixWord ++ tailWord_416160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416163 : List Nat := [1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 5]
def baseStart_416163 : Nat := 118140960795 + 416163 * 2 ^ 59
def prefixEnd_416163 : Nat := 4983230072969 + 3 ^ 40 * 416163 * 2
def baseEnd_416163 : Nat := 213691649617160494048607

theorem tailTrace_416163 : CollatzResearch.WordTrace tailWord_416163 prefixEnd_416163 213691649617160494048607 := by
  unfold tailWord_416163
  simp only [CollatzResearch.WordTrace]
  refine ⟨15178711591320000826941143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10119141060880000551294095 15178711591320000826941143)
  ·
    refine ⟨22768067386980001240411715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15178711591320000826941143 22768067386980001240411715)
    ·
      refine ⟨34152101080470001860617573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22768067386980001240411715 34152101080470001860617573)
      ·
        refine ⟨6403518952588125348865795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34152101080470001860617573 6403518952588125348865795)
        ·
          refine ⟨9605278428882188023298693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6403518952588125348865795 9605278428882188023298693)
          ·
            refine ⟨1800989705415410254368505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9605278428882188023298693 1800989705415410254368505)
            ·
              refine ⟨1350742279061557690776379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1800989705415410254368505 1350742279061557690776379)
              ·
                refine ⟨2026113418592336536164569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1350742279061557690776379 2026113418592336536164569)
                ·
                  refine ⟨1519585063944252402123427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2026113418592336536164569 1519585063944252402123427)
                  ·
                    refine ⟨2279377595916378603185141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1519585063944252402123427 2279377595916378603185141)
                    ·
                      refine ⟨213691649617160494048607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2279377595916378603185141 213691649617160494048607)
                      ·
                        rfl

theorem cell23_416163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_416163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_416163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_416163 prefixEnd_416163 := by exact prefixLift 416163
  have htrace : WordTrace (prefixWord ++ tailWord_416163) baseStart_416163 baseEnd_416163 := by
    simpa [prefixWord, tailWord_416163, baseEnd_416163] using wordTrace_append hprefix tailTrace_416163
  have hstable : (prefixWord ++ tailWord_416163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416163).length < 2 ^ (prefixWord ++ tailWord_416163).sum := by decide
  have hdescent : baseEnd_416163 < baseStart_416163 := by decide
  rcases family_descends (prefixWord ++ tailWord_416163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416250 : List Nat := [3, 1, 1, 1, 1, 2, 2, 3, 1, 6, 2]
def baseStart_416250 : Nat := 118140960795 + 416250 * 2 ^ 59
def prefixEnd_416250 : Nat := 4983230072969 + 3 ^ 40 * 416250 * 2
def baseEnd_416250 : Nat := 213736322434101653660707

theorem tailTrace_416250 : CollatzResearch.WordTrace tailWord_416250 prefixEnd_416250 213736322434101653660707 := by
  unfold tailWord_416250
  simp only [CollatzResearch.WordTrace]
  refine ⟨3795471185501203671339551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10121256494669876456905469 3795471185501203671339551)
  ·
    refine ⟨5693206778251805507009327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3795471185501203671339551 5693206778251805507009327)
    ·
      refine ⟨8539810167377708260513991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5693206778251805507009327 8539810167377708260513991)
      ·
        refine ⟨12809715251066562390770987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8539810167377708260513991 12809715251066562390770987)
        ·
          refine ⟨19214572876599843586156481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12809715251066562390770987 19214572876599843586156481)
          ·
            refine ⟨14410929657449882689617361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19214572876599843586156481 14410929657449882689617361)
            ·
              refine ⟨10808197243087412017213021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14410929657449882689617361 10808197243087412017213021)
              ·
                refine ⟨4053073966157779506454883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10808197243087412017213021 4053073966157779506454883)
                ·
                  refine ⟨6079610949236669259682325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4053073966157779506454883 6079610949236669259682325)
                  ·
                    refine ⟨284981763245468871547609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6079610949236669259682325 284981763245468871547609)
                    ·
                      refine ⟨213736322434101653660707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 284981763245468871547609 213736322434101653660707)
                      ·
                        rfl

theorem cell23_416250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 1, 6, 2].length) (baseStart_416250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_416250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_416250 prefixEnd_416250 := by exact prefixLift 416250
  have htrace : WordTrace (prefixWord ++ tailWord_416250) baseStart_416250 baseEnd_416250 := by
    simpa [prefixWord, tailWord_416250, baseEnd_416250] using wordTrace_append hprefix tailTrace_416250
  have hstable : (prefixWord ++ tailWord_416250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416250).length < 2 ^ (prefixWord ++ tailWord_416250).sum := by decide
  have hdescent : baseEnd_416250 < baseStart_416250 := by decide
  rcases family_descends (prefixWord ++ tailWord_416250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416290 : List Nat := [3, 3, 1, 1, 1, 1, 1, 6, 6]
def baseStart_416290 : Nat := 118140960795 + 416290 * 2 ^ 59
def prefixEnd_416290 : Nat := 4983230072969 + 3 ^ 40 * 416290 * 2
def baseEnd_416290 : Nat := 23750762406697944128947

theorem tailTrace_416290 : CollatzResearch.WordTrace tailWord_416290 prefixEnd_416290 23750762406697944128947 := by
  unfold tailWord_416290
  simp only [CollatzResearch.WordTrace]
  refine ⟨3795835915464975379203581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10122229107906601011209549 3795835915464975379203581)
  ·
    refine ⟨1423438468299365767201343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3795835915464975379203581 1423438468299365767201343)
    ·
      refine ⟨2135157702449048650802015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1423438468299365767201343 2135157702449048650802015)
      ·
        refine ⟨3202736553673572976203023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2135157702449048650802015 3202736553673572976203023)
        ·
          refine ⟨4804104830510359464304535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3202736553673572976203023 4804104830510359464304535)
          ·
            refine ⟨7206157245765539196456803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4804104830510359464304535 7206157245765539196456803)
            ·
              refine ⟨10809235868648308794685205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7206157245765539196456803 10809235868648308794685205)
              ·
                refine ⟨506682931342889474750869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10809235868648308794685205 506682931342889474750869)
                ·
                  refine ⟨23750762406697944128947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 506682931342889474750869 23750762406697944128947)
                  ·
                    rfl

theorem cell23_416290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_416290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_416290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_416290 prefixEnd_416290 := by exact prefixLift 416290
  have htrace : WordTrace (prefixWord ++ tailWord_416290) baseStart_416290 baseEnd_416290 := by
    simpa [prefixWord, tailWord_416290, baseEnd_416290] using wordTrace_append hprefix tailTrace_416290
  have hstable : (prefixWord ++ tailWord_416290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416290).length < 2 ^ (prefixWord ++ tailWord_416290).sum := by decide
  have hdescent : baseEnd_416290 < baseStart_416290 := by decide
  rcases family_descends (prefixWord ++ tailWord_416290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416293 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 1, 1, 8]
def baseStart_416293 : Nat := 118140960795 + 416293 * 2 ^ 59
def prefixEnd_416293 : Nat := 4983230072969 + 3 ^ 40 * 416293 * 2
def baseEnd_416293 : Nat := 213758402102244985423009

theorem tailTrace_416293 : CollatzResearch.WordTrace tailWord_416293 prefixEnd_416293 213758402102244985423009 := by
  unfold tailWord_416293
  simp only [CollatzResearch.WordTrace]
  refine ⟨15183453080849033029173533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10122302053899355352782355 15183453080849033029173533)
  ·
    refine ⟨5693794905318387385940075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15183453080849033029173533 5693794905318387385940075)
    ·
      refine ⟨8540692357977581078910113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5693794905318387385940075 8540692357977581078910113)
      ·
        refine ⟨6405519268483185809182585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8540692357977581078910113 6405519268483185809182585)
        ·
          refine ⟨4804139451362389356886939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6405519268483185809182585 4804139451362389356886939)
          ·
            refine ⟨7206209177043584035330409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4804139451362389356886939 7206209177043584035330409)
            ·
              refine ⟨5404656882782688026497807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7206209177043584035330409 5404656882782688026497807)
              ·
                refine ⟨8106985324174032039746711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5404656882782688026497807 8106985324174032039746711)
                ·
                  refine ⟨12160477986261048059620067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8106985324174032039746711 12160477986261048059620067)
                  ·
                    refine ⟨18240716979391572089430101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12160477986261048059620067 18240716979391572089430101)
                    ·
                      refine ⟨213758402102244985423009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 18240716979391572089430101 213758402102244985423009)
                      ·
                        rfl

theorem cell23_416293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_416293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_416293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_416293 prefixEnd_416293 := by exact prefixLift 416293
  have htrace : WordTrace (prefixWord ++ tailWord_416293) baseStart_416293 baseEnd_416293 := by
    simpa [prefixWord, tailWord_416293, baseEnd_416293] using wordTrace_append hprefix tailTrace_416293
  have hstable : (prefixWord ++ tailWord_416293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416293).length < 2 ^ (prefixWord ++ tailWord_416293).sum := by decide
  have hdescent : baseEnd_416293 < baseStart_416293 := by decide
  rcases family_descends (prefixWord ++ tailWord_416293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416363 : List Nat := [1, 1, 1, 1, 2, 2, 1, 14]
def baseStart_416363 : Nat := 118140960795 + 416363 * 2 ^ 59
def prefixEnd_416363 : Nat := 4983230072969 + 3 ^ 40 * 416363 * 2
def baseEnd_416363 : Nat := 7918309101779989316581

theorem tailTrace_416363 : CollatzResearch.WordTrace tailWord_416363 prefixEnd_416363 7918309101779989316581 := by
  unfold tailWord_416363
  simp only [CollatzResearch.WordTrace]
  refine ⟨15186006190595434984221743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10124004127063623322814495 15186006190595434984221743)
  ·
    refine ⟨22779009285893152476332615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15186006190595434984221743 22779009285893152476332615)
    ·
      refine ⟨34168513928839728714498923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22779009285893152476332615 34168513928839728714498923)
      ·
        refine ⟨51252770893259593071748385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34168513928839728714498923 51252770893259593071748385)
        ·
          refine ⟨38439578169944694803811289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51252770893259593071748385 38439578169944694803811289)
          ·
            refine ⟨28829683627458521102858467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38439578169944694803811289 28829683627458521102858467)
            ·
              refine ⟨43244525441187781654287701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28829683627458521102858467 43244525441187781654287701)
              ·
                refine ⟨7918309101779989316581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 14 43244525441187781654287701 7918309101779989316581)
                ·
                  rfl

theorem cell23_416363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 14].length) (baseStart_416363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_416363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_416363 prefixEnd_416363 := by exact prefixLift 416363
  have htrace : WordTrace (prefixWord ++ tailWord_416363) baseStart_416363 baseEnd_416363 := by
    simpa [prefixWord, tailWord_416363, baseEnd_416363] using wordTrace_append hprefix tailTrace_416363
  have hstable : (prefixWord ++ tailWord_416363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416363).length < 2 ^ (prefixWord ++ tailWord_416363).sum := by decide
  have hdescent : baseEnd_416363 < baseStart_416363 := by decide
  rcases family_descends (prefixWord ++ tailWord_416363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416367 : List Nat := [1, 1, 2, 1, 3, 2, 4, 3, 2, 4]
def baseStart_416367 : Nat := 118140960795 + 416367 * 2 ^ 59
def prefixEnd_416367 : Nat := 4983230072969 + 3 ^ 40 * 416367 * 2
def baseEnd_416367 : Nat := 71265466556892565299223

theorem tailTrace_416367 : CollatzResearch.WordTrace tailWord_416367 prefixEnd_416367 71265466556892565299223 := by
  unfold tailWord_416367
  simp only [CollatzResearch.WordTrace]
  refine ⟨15186152082580943667367355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10124101388387295778244903 15186152082580943667367355)
  ·
    refine ⟨22779228123871415501051033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15186152082580943667367355 22779228123871415501051033)
    ·
      refine ⟨17084421092903561625788275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22779228123871415501051033 17084421092903561625788275)
      ·
        refine ⟨25626631639355342438682413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17084421092903561625788275 25626631639355342438682413)
        ·
          refine ⟨9609986864758253414505905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25626631639355342438682413 9609986864758253414505905)
          ·
            refine ⟨7207490148568690060879429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9609986864758253414505905 7207490148568690060879429)
            ·
              refine ⟨1351404402856629386414893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7207490148568690060879429 1351404402856629386414893)
              ·
                refine ⟨506776651071236019905585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1351404402856629386414893 506776651071236019905585)
                ·
                  refine ⟨380082488303427014929189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 506776651071236019905585 380082488303427014929189)
                  ·
                    refine ⟨71265466556892565299223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 380082488303427014929189 71265466556892565299223)
                    ·
                      rfl

theorem cell23_416367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 3, 2, 4].length) (baseStart_416367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_416367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_416367 prefixEnd_416367 := by exact prefixLift 416367
  have htrace : WordTrace (prefixWord ++ tailWord_416367) baseStart_416367 baseEnd_416367 := by
    simpa [prefixWord, tailWord_416367, baseEnd_416367] using wordTrace_append hprefix tailTrace_416367
  have hstable : (prefixWord ++ tailWord_416367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416367).length < 2 ^ (prefixWord ++ tailWord_416367).sum := by decide
  have hdescent : baseEnd_416367 < baseStart_416367 := by decide
  rcases family_descends (prefixWord ++ tailWord_416367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416377 : List Nat := [1, 2, 1, 3, 3, 2, 2, 1, 3, 2, 3]
def baseStart_416377 : Nat := 118140960795 + 416377 * 2 ^ 59
def prefixEnd_416377 : Nat := 4983230072969 + 3 ^ 40 * 416377 * 2
def baseEnd_416377 : Nat := 213801534477222656772623

theorem tailTrace_416377 : CollatzResearch.WordTrace tailWord_416377 prefixEnd_416377 213801534477222656772623 := by
  unfold tailWord_416377
  simp only [CollatzResearch.WordTrace]
  refine ⟨15186516812544715375231385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10124344541696476916820923 15186516812544715375231385)
  ·
    refine ⟨11389887609408536531423539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15186516812544715375231385 11389887609408536531423539)
    ·
      refine ⟨17084831414112804797135309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11389887609408536531423539 17084831414112804797135309)
      ·
        refine ⟨6406811780292301798925741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17084831414112804797135309 6406811780292301798925741)
        ·
          refine ⟨2402554417609613174597153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6406811780292301798925741 2402554417609613174597153)
          ·
            refine ⟨1801915813207209880947865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2402554417609613174597153 1801915813207209880947865)
            ·
              refine ⟨1351436859905407410710899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1801915813207209880947865 1351436859905407410710899)
              ·
                refine ⟨2027155289858111116066349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1351436859905407410710899 2027155289858111116066349)
                ·
                  refine ⟨760183233696791668524881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2027155289858111116066349 760183233696791668524881)
                  ·
                    refine ⟨570137425272593751393661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 760183233696791668524881 570137425272593751393661)
                    ·
                      refine ⟨213801534477222656772623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 570137425272593751393661 213801534477222656772623)
                      ·
                        rfl

theorem cell23_416377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 2, 3].length) (baseStart_416377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_416377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_416377 prefixEnd_416377 := by exact prefixLift 416377
  have htrace : WordTrace (prefixWord ++ tailWord_416377) baseStart_416377 baseEnd_416377 := by
    simpa [prefixWord, tailWord_416377, baseEnd_416377] using wordTrace_append hprefix tailTrace_416377
  have hstable : (prefixWord ++ tailWord_416377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416377).length < 2 ^ (prefixWord ++ tailWord_416377).sum := by decide
  have hdescent : baseEnd_416377 < baseStart_416377 := by decide
  rcases family_descends (prefixWord ++ tailWord_416377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416437 : List Nat := [1, 3, 3, 3, 1, 1, 1, 1, 2, 2, 5]
def baseStart_416437 : Nat := 118140960795 + 416437 * 2 ^ 59
def prefixEnd_416437 : Nat := 4983230072969 + 3 ^ 40 * 416437 * 2
def baseEnd_416437 : Nat := 213832343316492422022347

theorem tailTrace_416437 : CollatzResearch.WordTrace tailWord_416437 prefixEnd_416437 213832343316492422022347 := by
  unfold tailWord_416437
  simp only [CollatzResearch.WordTrace]
  refine ⟨15188705192327345622415565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10125803461551563748277043 15188705192327345622415565)
  ·
    refine ⟨5695764447122754608405837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15188705192327345622415565 5695764447122754608405837)
    ·
      refine ⟨2135911667671032978152189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5695764447122754608405837 2135911667671032978152189)
      ·
        refine ⟨800966875376637366807071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2135911667671032978152189 800966875376637366807071)
        ·
          refine ⟨1201450313064956050210607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 800966875376637366807071 1201450313064956050210607)
          ·
            refine ⟨1802175469597434075315911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1201450313064956050210607 1802175469597434075315911)
            ·
              refine ⟨2703263204396151112973867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1802175469597434075315911 2703263204396151112973867)
              ·
                refine ⟨4054894806594226669460801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2703263204396151112973867 4054894806594226669460801)
                ·
                  refine ⟨3041171104945670002095601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4054894806594226669460801 3041171104945670002095601)
                  ·
                    refine ⟨2280878328709252501571701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3041171104945670002095601 2280878328709252501571701)
                    ·
                      refine ⟨213832343316492422022347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2280878328709252501571701 213832343316492422022347)
                      ·
                        rfl

theorem cell23_416437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_416437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_416437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_416437 prefixEnd_416437 := by exact prefixLift 416437
  have htrace : WordTrace (prefixWord ++ tailWord_416437) baseStart_416437 baseEnd_416437 := by
    simpa [prefixWord, tailWord_416437, baseEnd_416437] using wordTrace_append hprefix tailTrace_416437
  have hstable : (prefixWord ++ tailWord_416437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416437).length < 2 ^ (prefixWord ++ tailWord_416437).sum := by decide
  have hdescent : baseEnd_416437 < baseStart_416437 := by decide
  rcases family_descends (prefixWord ++ tailWord_416437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416597 : List Nat := [1, 3, 2, 2, 2, 1, 1, 2, 1, 2, 6]
def baseStart_416597 : Nat := 118140960795 + 416597 * 2 ^ 59
def prefixEnd_416597 : Nat := 4983230072969 + 3 ^ 40 * 416597 * 2
def baseEnd_416597 : Nat := 213914500221211796021611

theorem tailTrace_416597 : CollatzResearch.WordTrace tailWord_416597 prefixEnd_416597 213914500221211796021611 := by
  unfold tailWord_416597
  simp only [CollatzResearch.WordTrace]
  refine ⟨15194540871747692948240045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10129693914498461965493363 15194540871747692948240045)
  ·
    refine ⟨5697952826905384855590017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15194540871747692948240045 5697952826905384855590017)
    ·
      refine ⟨4273464620179038641692513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5697952826905384855590017 4273464620179038641692513)
      ·
        refine ⟨3205098465134278981269385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4273464620179038641692513 3205098465134278981269385)
        ·
          refine ⟨2403823848850709235952039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3205098465134278981269385 2403823848850709235952039)
          ·
            refine ⟨3605735773276063853928059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2403823848850709235952039 3605735773276063853928059)
            ·
              refine ⟨5408603659914095780892089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3605735773276063853928059 5408603659914095780892089)
              ·
                refine ⟨4056452744935571835669067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5408603659914095780892089 4056452744935571835669067)
                ·
                  refine ⟨6084679117403357753503601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4056452744935571835669067 6084679117403357753503601)
                  ·
                    refine ⟨4563509338052518315127701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6084679117403357753503601 4563509338052518315127701)
                    ·
                      refine ⟨213914500221211796021611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4563509338052518315127701 213914500221211796021611)
                      ·
                        rfl

theorem cell23_416597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_416597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_416597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_416597 prefixEnd_416597 := by exact prefixLift 416597
  have htrace : WordTrace (prefixWord ++ tailWord_416597) baseStart_416597 baseEnd_416597 := by
    simpa [prefixWord, tailWord_416597, baseEnd_416597] using wordTrace_append hprefix tailTrace_416597
  have hstable : (prefixWord ++ tailWord_416597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416597).length < 2 ^ (prefixWord ++ tailWord_416597).sum := by decide
  have hdescent : baseEnd_416597 < baseStart_416597 := by decide
  rcases family_descends (prefixWord ++ tailWord_416597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416624 : List Nat := [2, 1, 1, 1, 4, 1, 4, 3, 1, 5]
def baseStart_416624 : Nat := 118140960795 + 416624 * 2 ^ 59
def prefixEnd_416624 : Nat := 4983230072969 + 3 ^ 40 * 416624 * 2
def baseEnd_416624 : Nat := 71309454732961063461329

theorem tailTrace_416624 : CollatzResearch.WordTrace tailWord_416624 prefixEnd_416624 71309454732961063461329 := by
  unfold tailWord_416624
  simp only [CollatzResearch.WordTrace]
  refine ⟨7597762821324938279736463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10130350428433251039648617 7597762821324938279736463)
  ·
    refine ⟨11396644231987407419604695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7597762821324938279736463 11396644231987407419604695)
    ·
      refine ⟨17094966347981111129407043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11396644231987407419604695 17094966347981111129407043)
      ·
        refine ⟨25642449521971666694110565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17094966347981111129407043 25642449521971666694110565)
        ·
          refine ⟨4807959285369687505145731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25642449521971666694110565 4807959285369687505145731)
          ·
            refine ⟨7211938928054531257718597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4807959285369687505145731 7211938928054531257718597)
            ·
              refine ⟨1352238549010224610822237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7211938928054531257718597 1352238549010224610822237)
              ·
                refine ⟨507089455878834229058339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1352238549010224610822237 507089455878834229058339)
                ·
                  refine ⟨760634183818251343587509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 507089455878834229058339 760634183818251343587509)
                  ·
                    refine ⟨71309454732961063461329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 760634183818251343587509 71309454732961063461329)
                    ·
                      rfl

theorem cell23_416624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 3, 1, 5].length) (baseStart_416624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_416624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_416624 prefixEnd_416624 := by exact prefixLift 416624
  have htrace : WordTrace (prefixWord ++ tailWord_416624) baseStart_416624 baseEnd_416624 := by
    simpa [prefixWord, tailWord_416624, baseEnd_416624] using wordTrace_append hprefix tailTrace_416624
  have hstable : (prefixWord ++ tailWord_416624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416624).length < 2 ^ (prefixWord ++ tailWord_416624).sum := by decide
  have hdescent : baseEnd_416624 < baseStart_416624 := by decide
  rcases family_descends (prefixWord ++ tailWord_416624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416644 : List Nat := [2, 3, 2, 1, 1, 1, 1, 4, 3, 1, 4]
def baseStart_416644 : Nat := 118140960795 + 416644 * 2 ^ 59
def prefixEnd_416644 : Nat := 4983230072969 + 3 ^ 40 * 416644 * 2
def baseEnd_416644 : Nat := 213938633811973112133895

theorem tailTrace_416644 : CollatzResearch.WordTrace tailWord_416644 prefixEnd_416644 213938633811973112133895 := by
  unfold tailWord_416644
  simp only [CollatzResearch.WordTrace]
  refine ⟨7598127551288709987600493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10130836735051613316800657 7598127551288709987600493)
  ·
    refine ⟨2849297831733266245350185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7598127551288709987600493 2849297831733266245350185)
    ·
      refine ⟨2136973373799949684012639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2849297831733266245350185 2136973373799949684012639)
      ·
        refine ⟨3205460060699924526018959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2136973373799949684012639 3205460060699924526018959)
        ·
          refine ⟨4808190091049886789028439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3205460060699924526018959 4808190091049886789028439)
          ·
            refine ⟨7212285136574830183542659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4808190091049886789028439 7212285136574830183542659)
            ·
              refine ⟨10818427704862245275313989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7212285136574830183542659 10818427704862245275313989)
              ·
                refine ⟨2028455194661670989121373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10818427704862245275313989 2028455194661670989121373)
                ·
                  refine ⟨760670697998126620920515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2028455194661670989121373 760670697998126620920515)
                  ·
                    refine ⟨1141006046997189931380773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 760670697998126620920515 1141006046997189931380773)
                    ·
                      refine ⟨213938633811973112133895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1141006046997189931380773 213938633811973112133895)
                      ·
                        rfl

theorem cell23_416644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_416644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_416644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_416644 prefixEnd_416644 := by exact prefixLift 416644
  have htrace : WordTrace (prefixWord ++ tailWord_416644) baseStart_416644 baseEnd_416644 := by
    simpa [prefixWord, tailWord_416644, baseEnd_416644] using wordTrace_append hprefix tailTrace_416644
  have hstable : (prefixWord ++ tailWord_416644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416644).length < 2 ^ (prefixWord ++ tailWord_416644).sum := by decide
  have hdescent : baseEnd_416644 < baseStart_416644 := by decide
  rcases family_descends (prefixWord ++ tailWord_416644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416661 : List Nat := [1, 3, 2, 1, 1, 4, 3, 2, 1, 1, 4]
def baseStart_416661 : Nat := 118140960795 + 416661 * 2 ^ 59
def prefixEnd_416661 : Nat := 4983230072969 + 3 ^ 40 * 416661 * 2
def baseEnd_416661 : Nat := 213947362983099545621317

theorem tailTrace_416661 : CollatzResearch.WordTrace tailWord_416661 prefixEnd_416661 213947362983099545621317 := by
  unfold tailWord_416661
  simp only [CollatzResearch.WordTrace]
  refine ⟨15196875143515831878569837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10131250095677221252379891 15196875143515831878569837)
  ·
    refine ⟨5698828178818436954463689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15196875143515831878569837 5698828178818436954463689)
    ·
      refine ⟨4274121134113827715847767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5698828178818436954463689 4274121134113827715847767)
      ·
        refine ⟨6411181701170741573771651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4274121134113827715847767 6411181701170741573771651)
        ·
          refine ⟨9616772551756112360657477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6411181701170741573771651 9616772551756112360657477)
          ·
            refine ⟨1803144853454271067623277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9616772551756112360657477 1803144853454271067623277)
            ·
              refine ⟨676179320045351650358729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1803144853454271067623277 676179320045351650358729)
              ·
                refine ⟨507134490034013737769047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 676179320045351650358729 507134490034013737769047)
                ·
                  refine ⟨760701735051020606653571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 507134490034013737769047 760701735051020606653571)
                  ·
                    refine ⟨1141052602576530909980357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 760701735051020606653571 1141052602576530909980357)
                    ·
                      refine ⟨213947362983099545621317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1141052602576530909980357 213947362983099545621317)
                      ·
                        rfl

theorem cell23_416661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 1, 4].length) (baseStart_416661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_416661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_416661 prefixEnd_416661 := by exact prefixLift 416661
  have htrace : WordTrace (prefixWord ++ tailWord_416661) baseStart_416661 baseEnd_416661 := by
    simpa [prefixWord, tailWord_416661, baseEnd_416661] using wordTrace_append hprefix tailTrace_416661
  have hstable : (prefixWord ++ tailWord_416661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416661).length < 2 ^ (prefixWord ++ tailWord_416661).sum := by decide
  have hdescent : baseEnd_416661 < baseStart_416661 := by decide
  rcases family_descends (prefixWord ++ tailWord_416661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416687 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 6]
def baseStart_416687 : Nat := 118140960795 + 416687 * 2 ^ 59
def prefixEnd_416687 : Nat := 4983230072969 + 3 ^ 40 * 416687 * 2
def baseEnd_416687 : Nat := 213960713480116443896197

theorem tailTrace_416687 : CollatzResearch.WordTrace tailWord_416687 prefixEnd_416687 213960713480116443896197 := by
  unfold tailWord_416687
  simp only [CollatzResearch.WordTrace]
  refine ⟨15197823441421638319016315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10131882294281092212677543 15197823441421638319016315)
  ·
    refine ⟨22796735162132457478524473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15197823441421638319016315 22796735162132457478524473)
    ·
      refine ⟨17097551371599343108893355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22796735162132457478524473 17097551371599343108893355)
      ·
        refine ⟨25646327057399014663340033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17097551371599343108893355 25646327057399014663340033)
        ·
          refine ⟨19234745293049260997505025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25646327057399014663340033 19234745293049260997505025)
          ·
            refine ⟨14426058969786945748128769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19234745293049260997505025 14426058969786945748128769)
            ·
              refine ⟨10819544227340209311096577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14426058969786945748128769 10819544227340209311096577)
              ·
                refine ⟨8114658170505156983322433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10819544227340209311096577 8114658170505156983322433)
                ·
                  refine ⟨6085993627878867737491825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8114658170505156983322433 6085993627878867737491825)
                  ·
                    refine ⟨4564495220909150803118869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6085993627878867737491825 4564495220909150803118869)
                    ·
                      refine ⟨213960713480116443896197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4564495220909150803118869 213960713480116443896197)
                      ·
                        rfl

theorem cell23_416687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 6].length) (baseStart_416687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_416687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_416687 prefixEnd_416687 := by exact prefixLift 416687
  have htrace : WordTrace (prefixWord ++ tailWord_416687) baseStart_416687 baseEnd_416687 := by
    simpa [prefixWord, tailWord_416687, baseEnd_416687] using wordTrace_append hprefix tailTrace_416687
  have hstable : (prefixWord ++ tailWord_416687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416687).length < 2 ^ (prefixWord ++ tailWord_416687).sum := by decide
  have hdescent : baseEnd_416687 < baseStart_416687 := by decide
  rcases family_descends (prefixWord ++ tailWord_416687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416689 : List Nat := [1, 2, 2, 4, 4, 1, 2, 2, 1, 1, 3]
def baseStart_416689 : Nat := 118140960795 + 416689 * 2 ^ 59
def prefixEnd_416689 : Nat := 4983230072969 + 3 ^ 40 * 416689 * 2
def baseEnd_416689 : Nat := 213961740441425436071189

theorem tailTrace_416689 : CollatzResearch.WordTrace tailWord_416689 prefixEnd_416689 213961740441425436071189 := by
  unfold tailWord_416689
  simp only [CollatzResearch.WordTrace]
  refine ⟨15197896387414392660589121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10131930924942928440392747 15197896387414392660589121)
  ·
    refine ⟨11398422290560794495441841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15197896387414392660589121 11398422290560794495441841)
    ·
      refine ⟨8548816717920595871581381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11398422290560794495441841 8548816717920595871581381)
      ·
        refine ⟨1602903134610111725921509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8548816717920595871581381 1602903134610111725921509)
        ·
          refine ⟨300544337739395948610283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1602903134610111725921509 300544337739395948610283)
          ·
            refine ⟨450816506609093922915425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300544337739395948610283 450816506609093922915425)
            ·
              refine ⟨338112379956820442186569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 450816506609093922915425 338112379956820442186569)
              ·
                refine ⟨253584284967615331639927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 338112379956820442186569 253584284967615331639927)
                ·
                  refine ⟨380376427451422997459891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 253584284967615331639927 380376427451422997459891)
                  ·
                    refine ⟨570564641177134496189837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 380376427451422997459891 570564641177134496189837)
                    ·
                      refine ⟨213961740441425436071189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 570564641177134496189837 213961740441425436071189)
                      ·
                        rfl

theorem cell23_416689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_416689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_416689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_416689 prefixEnd_416689 := by exact prefixLift 416689
  have htrace : WordTrace (prefixWord ++ tailWord_416689) baseStart_416689 baseEnd_416689 := by
    simpa [prefixWord, tailWord_416689, baseEnd_416689] using wordTrace_append hprefix tailTrace_416689
  have hstable : (prefixWord ++ tailWord_416689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416689).length < 2 ^ (prefixWord ++ tailWord_416689).sum := by decide
  have hdescent : baseEnd_416689 < baseStart_416689 := by decide
  rcases family_descends (prefixWord ++ tailWord_416689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416701 : List Nat := [1, 4, 1, 2, 4, 2, 1, 8]
def baseStart_416701 : Nat := 118140960795 + 416701 * 2 ^ 59
def prefixEnd_416701 : Nat := 4983230072969 + 3 ^ 40 * 416701 * 2
def baseEnd_416701 : Nat := 7924737118862199597079

theorem tailTrace_416701 : CollatzResearch.WordTrace tailWord_416701 prefixEnd_416701 7924737118862199597079 := by
  unfold tailWord_416701
  simp only [CollatzResearch.WordTrace]
  refine ⟨15198334063370918710025957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10132222708913945806683971 15198334063370918710025957)
  ·
    refine ⟨2849687636882047258129867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15198334063370918710025957 2849687636882047258129867)
    ·
      refine ⟨4274531455323070887194801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2849687636882047258129867 4274531455323070887194801)
      ·
        refine ⟨3205898591492303165396101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4274531455323070887194801 3205898591492303165396101)
        ·
          refine ⟨601105985904806843511769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3205898591492303165396101 601105985904806843511769)
          ·
            refine ⟨450829489428605132633827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 601105985904806843511769 450829489428605132633827)
            ·
              refine ⟨676244234142907698950741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450829489428605132633827 676244234142907698950741)
              ·
                refine ⟨7924737118862199597079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 676244234142907698950741 7924737118862199597079)
                ·
                  rfl

theorem cell23_416701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 8].length) (baseStart_416701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_416701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_416701 prefixEnd_416701 := by exact prefixLift 416701
  have htrace : WordTrace (prefixWord ++ tailWord_416701) baseStart_416701 baseEnd_416701 := by
    simpa [prefixWord, tailWord_416701, baseEnd_416701] using wordTrace_append hprefix tailTrace_416701
  have hstable : (prefixWord ++ tailWord_416701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416701).length < 2 ^ (prefixWord ++ tailWord_416701).sum := by decide
  have hdescent : baseEnd_416701 < baseStart_416701 := by decide
  rcases family_descends (prefixWord ++ tailWord_416701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416721 : List Nat := [1, 2, 2, 1, 2, 1, 3, 3, 3, 3, 2]
def baseStart_416721 : Nat := 118140960795 + 416721 * 2 ^ 59
def prefixEnd_416721 : Nat := 4983230072969 + 3 ^ 40 * 416721 * 2
def baseEnd_416721 : Nat := 213978171822369310871041

theorem tailTrace_416721 : CollatzResearch.WordTrace tailWord_416721 prefixEnd_416721 213978171822369310871041 := by
  unfold tailWord_416721
  simp only [CollatzResearch.WordTrace]
  refine ⟨15199063523298462125754017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10132709015532308083836011 15199063523298462125754017)
  ·
    refine ⟨11399297642473846594315513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15199063523298462125754017 11399297642473846594315513)
    ·
      refine ⟨8549473231855384945736635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11399297642473846594315513 8549473231855384945736635)
      ·
        refine ⟨12824209847783077418604953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8549473231855384945736635 12824209847783077418604953)
        ·
          refine ⟨9618157385837308063953715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12824209847783077418604953 9618157385837308063953715)
          ·
            refine ⟨14427236078755962095930573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9618157385837308063953715 14427236078755962095930573)
            ·
              refine ⟨5410213529533485785973965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14427236078755962095930573 5410213529533485785973965)
              ·
                refine ⟨2028830073575057169740237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5410213529533485785973965 2028830073575057169740237)
                ·
                  refine ⟨760811277590646438652589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2028830073575057169740237 760811277590646438652589)
                  ·
                    refine ⟨285304229096492414494721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 760811277590646438652589 285304229096492414494721)
                    ·
                      refine ⟨213978171822369310871041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 285304229096492414494721 213978171822369310871041)
                      ·
                        rfl

theorem cell23_416721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 3, 2].length) (baseStart_416721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_416721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_416721 prefixEnd_416721 := by exact prefixLift 416721
  have htrace : WordTrace (prefixWord ++ tailWord_416721) baseStart_416721 baseEnd_416721 := by
    simpa [prefixWord, tailWord_416721, baseEnd_416721] using wordTrace_append hprefix tailTrace_416721
  have hstable : (prefixWord ++ tailWord_416721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416721).length < 2 ^ (prefixWord ++ tailWord_416721).sum := by decide
  have hdescent : baseEnd_416721 < baseStart_416721 := by decide
  rcases family_descends (prefixWord ++ tailWord_416721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416744 : List Nat := [2, 1, 4, 1, 1, 1, 3, 2, 2, 6]
def baseStart_416744 : Nat := 118140960795 + 416744 * 2 ^ 59
def prefixEnd_416744 : Nat := 4983230072969 + 3 ^ 40 * 416744 * 2
def baseEnd_416744 : Nat := 71329993959140906961145

theorem tailTrace_416744 : CollatzResearch.WordTrace tailWord_416744 prefixEnd_416744 71329993959140906961145 := by
  unfold tailWord_416744
  simp only [CollatzResearch.WordTrace]
  refine ⟨7599951201107568526920643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10133268268143424702560857 7599951201107568526920643)
  ·
    refine ⟨11399926801661352790380965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7599951201107568526920643 11399926801661352790380965)
    ·
      refine ⟨2137486275311503648196431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11399926801661352790380965 2137486275311503648196431)
      ·
        refine ⟨3206229412967255472294647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2137486275311503648196431 3206229412967255472294647)
        ·
          refine ⟨4809344119450883208441971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3206229412967255472294647 4809344119450883208441971)
          ·
            refine ⟨7214016179176324812662957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4809344119450883208441971 7214016179176324812662957)
            ·
              refine ⟨2705256067191121804748609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7214016179176324812662957 2705256067191121804748609)
              ·
                refine ⟨2028942050393341353561457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2705256067191121804748609 2028942050393341353561457)
                ·
                  refine ⟨1521706537795006015171093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2028942050393341353561457 1521706537795006015171093)
                  ·
                    refine ⟨71329993959140906961145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1521706537795006015171093 71329993959140906961145)
                    ·
                      rfl

theorem cell23_416744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_416744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_416744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_416744 prefixEnd_416744 := by exact prefixLift 416744
  have htrace : WordTrace (prefixWord ++ tailWord_416744) baseStart_416744 baseEnd_416744 := by
    simpa [prefixWord, tailWord_416744, baseEnd_416744] using wordTrace_append hprefix tailTrace_416744
  have hstable : (prefixWord ++ tailWord_416744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416744).length < 2 ^ (prefixWord ++ tailWord_416744).sum := by decide
  have hdescent : baseEnd_416744 < baseStart_416744 := by decide
  rcases family_descends (prefixWord ++ tailWord_416744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416756 : List Nat := [2, 6, 2, 1, 1, 1, 3, 1, 2, 4]
def baseStart_416756 : Nat := 118140960795 + 416756 * 2 ^ 59
def prefixEnd_416756 : Nat := 4983230072969 + 3 ^ 40 * 416756 * 2
def baseEnd_416756 : Nat := 71332047881758891311127

theorem tailTrace_416756 : CollatzResearch.WordTrace tailWord_416756 prefixEnd_416756 71332047881758891311127 := by
  unfold tailWord_416756
  simp only [CollatzResearch.WordTrace]
  refine ⟨7600170039085831551639061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10133560052114442068852081 7600170039085831551639061)
  ·
    refine ⟨356257970582148353983081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7600170039085831551639061 356257970582148353983081)
    ·
      refine ⟨267193477936611265487311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356257970582148353983081 267193477936611265487311)
      ·
        refine ⟨400790216904916898230967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267193477936611265487311 400790216904916898230967)
        ·
          refine ⟨601185325357375347346451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400790216904916898230967 601185325357375347346451)
          ·
            refine ⟨901777988036063021019677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 601185325357375347346451 901777988036063021019677)
            ·
              refine ⟨338166745513523632882379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 901777988036063021019677 338166745513523632882379)
              ·
                refine ⟨507250118270285449323569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 338166745513523632882379 507250118270285449323569)
                ·
                  refine ⟨380437588702714086992677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 507250118270285449323569 380437588702714086992677)
                  ·
                    refine ⟨71332047881758891311127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 380437588702714086992677 71332047881758891311127)
                    ·
                      rfl

theorem cell23_416756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_416756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_416756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_416756 prefixEnd_416756 := by exact prefixLift 416756
  have htrace : WordTrace (prefixWord ++ tailWord_416756) baseStart_416756 baseEnd_416756 := by
    simpa [prefixWord, tailWord_416756, baseEnd_416756] using wordTrace_append hprefix tailTrace_416756
  have hstable : (prefixWord ++ tailWord_416756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416756).length < 2 ^ (prefixWord ++ tailWord_416756).sum := by decide
  have hdescent : baseEnd_416756 < baseStart_416756 := by decide
  rcases family_descends (prefixWord ++ tailWord_416756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416811 : List Nat := [1, 1, 1, 1, 2, 1, 6, 1, 2, 5, 2]
def baseStart_416811 : Nat := 118140960795 + 416811 * 2 ^ 59
def prefixEnd_416811 : Nat := 4983230072969 + 3 ^ 40 * 416811 * 2
def baseEnd_416811 : Nat := 214024385081273958745627

theorem tailTrace_416811 : CollatzResearch.WordTrace tailWord_416811 prefixEnd_416811 214024385081273958745627 := by
  unfold tailWord_416811
  simp only [CollatzResearch.WordTrace]
  refine ⟨15202346092972407496530287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10134897395314938331020191 15202346092972407496530287)
  ·
    refine ⟨22803519139458611244795431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15202346092972407496530287 22803519139458611244795431)
    ·
      refine ⟨34205278709187916867193147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22803519139458611244795431 34205278709187916867193147)
      ·
        refine ⟨51307918063781875300789721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34205278709187916867193147 51307918063781875300789721)
        ·
          refine ⟨38480938547836406475592291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51307918063781875300789721 38480938547836406475592291)
          ·
            refine ⟨57721407821754609713388437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38480938547836406475592291 57721407821754609713388437)
            ·
              refine ⟨2705690991644747330315083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 57721407821754609713388437 2705690991644747330315083)
              ·
                refine ⟨4058536487467120995472625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2705690991644747330315083 4058536487467120995472625)
                ·
                  refine ⟨3043902365600340746604469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4058536487467120995472625 3043902365600340746604469)
                  ·
                    refine ⟨285365846775031944994169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3043902365600340746604469 285365846775031944994169)
                    ·
                      refine ⟨214024385081273958745627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 285365846775031944994169 214024385081273958745627)
                      ·
                        rfl

theorem cell23_416811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 5, 2].length) (baseStart_416811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_416811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_416811 prefixEnd_416811 := by exact prefixLift 416811
  have htrace : WordTrace (prefixWord ++ tailWord_416811) baseStart_416811 baseEnd_416811 := by
    simpa [prefixWord, tailWord_416811, baseEnd_416811] using wordTrace_append hprefix tailTrace_416811
  have hstable : (prefixWord ++ tailWord_416811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416811).length < 2 ^ (prefixWord ++ tailWord_416811).sum := by decide
  have hdescent : baseEnd_416811 < baseStart_416811 := by decide
  rcases family_descends (prefixWord ++ tailWord_416811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416841 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 3, 6, 2]
def baseStart_416841 : Nat := 118140960795 + 416841 * 2 ^ 59
def prefixEnd_416841 : Nat := 4983230072969 + 3 ^ 40 * 416841 * 2
def baseEnd_416841 : Nat := 214039789500908841370489

theorem tailTrace_416841 : CollatzResearch.WordTrace tailWord_416841 prefixEnd_416841 214039789500908841370489 := by
  unfold tailWord_416841
  simp only [CollatzResearch.WordTrace]
  refine ⟨15203440282863722620122377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10135626855242481746748251 15203440282863722620122377)
  ·
    refine ⟨11402580212147791965091783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15203440282863722620122377 11402580212147791965091783)
    ·
      refine ⟨17103870318221687947637675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11402580212147791965091783 17103870318221687947637675)
      ·
        refine ⟨25655805477332531921456513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17103870318221687947637675 25655805477332531921456513)
        ·
          refine ⟨19241854107999398941092385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25655805477332531921456513 19241854107999398941092385)
          ·
            refine ⟨14431390580999549205819289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19241854107999398941092385 14431390580999549205819289)
            ·
              refine ⟨10823542935749661904364467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14431390580999549205819289 10823542935749661904364467)
              ·
                refine ⟨16235314403624492856546701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10823542935749661904364467 16235314403624492856546701)
                ·
                  refine ⟨6088242901359184821205013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16235314403624492856546701 6088242901359184821205013)
                  ·
                    refine ⟨285386386001211788493985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6088242901359184821205013 285386386001211788493985)
                    ·
                      refine ⟨214039789500908841370489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 285386386001211788493985 214039789500908841370489)
                      ·
                        rfl

theorem cell23_416841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 6, 2].length) (baseStart_416841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_416841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_416841 prefixEnd_416841 := by exact prefixLift 416841
  have htrace : WordTrace (prefixWord ++ tailWord_416841) baseStart_416841 baseEnd_416841 := by
    simpa [prefixWord, tailWord_416841, baseEnd_416841] using wordTrace_append hprefix tailTrace_416841
  have hstable : (prefixWord ++ tailWord_416841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416841).length < 2 ^ (prefixWord ++ tailWord_416841).sum := by decide
  have hdescent : baseEnd_416841 < baseStart_416841 := by decide
  rcases family_descends (prefixWord ++ tailWord_416841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416862 : List Nat := [4, 4, 1, 1, 1, 1, 1, 1, 2, 5, 2]
def baseStart_416862 : Nat := 118140960795 + 416862 * 2 ^ 59
def prefixEnd_416862 : Nat := 4983230072969 + 3 ^ 40 * 416862 * 2
def baseEnd_416862 : Nat := 214050572594653259207893

theorem tailTrace_416862 : CollatzResearch.WordTrace tailWord_416862 prefixEnd_416862 214050572594653259207893 := by
  unfold tailWord_416862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1900525776973455400829605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10136137477191762137757893 1900525776973455400829605)
  ·
    refine ⟨356348583182522887655551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1900525776973455400829605 356348583182522887655551)
    ·
      refine ⟨534522874773784331483327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356348583182522887655551 534522874773784331483327)
      ·
        refine ⟨801784312160676497224991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 534522874773784331483327 801784312160676497224991)
        ·
          refine ⟨1202676468241014745837487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 801784312160676497224991 1202676468241014745837487)
          ·
            refine ⟨1804014702361522118756231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1202676468241014745837487 1804014702361522118756231)
            ·
              refine ⟨2706022053542283178134347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1804014702361522118756231 2706022053542283178134347)
              ·
                refine ⟨4059033080313424767201521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2706022053542283178134347 4059033080313424767201521)
                ·
                  refine ⟨3044274810235068575401141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4059033080313424767201521 3044274810235068575401141)
                  ·
                    refine ⟨285400763459537678943857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3044274810235068575401141 285400763459537678943857)
                    ·
                      refine ⟨214050572594653259207893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 285400763459537678943857 214050572594653259207893)
                      ·
                        rfl

theorem cell23_416862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_416862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_416862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_416862 prefixEnd_416862 := by exact prefixLift 416862
  have htrace : WordTrace (prefixWord ++ tailWord_416862) baseStart_416862 baseEnd_416862 := by
    simpa [prefixWord, tailWord_416862, baseEnd_416862] using wordTrace_append hprefix tailTrace_416862
  have hstable : (prefixWord ++ tailWord_416862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416862).length < 2 ^ (prefixWord ++ tailWord_416862).sum := by decide
  have hdescent : baseEnd_416862 < baseStart_416862 := by decide
  rcases family_descends (prefixWord ++ tailWord_416862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416925 : List Nat := [1, 4, 2, 1, 1, 2, 4, 1, 3, 1, 3]
def baseStart_416925 : Nat := 118140960795 + 416925 * 2 ^ 59
def prefixEnd_416925 : Nat := 4983230072969 + 3 ^ 40 * 416925 * 2
def baseEnd_416925 : Nat := 214082921875886512720103

theorem tailTrace_416925 : CollatzResearch.WordTrace tailWord_416925 prefixEnd_416925 214082921875886512720103 := by
  unfold tailWord_416925
  simp only [CollatzResearch.WordTrace]
  refine ⟨15206504014559404966180229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10137669343039603310786819 15206504014559404966180229)
  ·
    refine ⟨2851219502729888431158793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15206504014559404966180229 2851219502729888431158793)
    ·
      refine ⟨2138414627047416323369095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2851219502729888431158793 2138414627047416323369095)
      ·
        refine ⟨3207621940571124485053643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2138414627047416323369095 3207621940571124485053643)
        ·
          refine ⟨4811432910856686727580465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3207621940571124485053643 4811432910856686727580465)
          ·
            refine ⟨3608574683142515045685349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4811432910856686727580465 3608574683142515045685349)
            ·
              refine ⟨676607753089221571066003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3608574683142515045685349 676607753089221571066003)
              ·
                refine ⟨1014911629633832356599005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 676607753089221571066003 1014911629633832356599005)
                ·
                  refine ⟨380591861112687133724627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1014911629633832356599005 380591861112687133724627)
                  ·
                    refine ⟨570887791669030700586941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 380591861112687133724627 570887791669030700586941)
                    ·
                      refine ⟨214082921875886512720103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 570887791669030700586941 214082921875886512720103)
                      ·
                        rfl

theorem cell23_416925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_416925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_416925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_416925 prefixEnd_416925 := by exact prefixLift 416925
  have htrace : WordTrace (prefixWord ++ tailWord_416925) baseStart_416925 baseEnd_416925 := by
    simpa [prefixWord, tailWord_416925, baseEnd_416925] using wordTrace_append hprefix tailTrace_416925
  have hstable : (prefixWord ++ tailWord_416925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416925).length < 2 ^ (prefixWord ++ tailWord_416925).sum := by decide
  have hdescent : baseEnd_416925 < baseStart_416925 := by decide
  rcases family_descends (prefixWord ++ tailWord_416925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416931 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 4]
def baseStart_416931 : Nat := 118140960795 + 416931 * 2 ^ 59
def prefixEnd_416931 : Nat := 4983230072969 + 3 ^ 40 * 416931 * 2
def baseEnd_416931 : Nat := 214086002759813489245075

theorem tailTrace_416931 : CollatzResearch.WordTrace tailWord_416931 prefixEnd_416931 214086002759813489245075 := by
  unfold tailWord_416931
  simp only [CollatzResearch.WordTrace]
  refine ⟨15206722852537667990898647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10137815235025111993932431 15206722852537667990898647)
  ·
    refine ⟨22810084278806501986347971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15206722852537667990898647 22810084278806501986347971)
    ·
      refine ⟨34215126418209752979521957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22810084278806501986347971 34215126418209752979521957)
      ·
        refine ⟨6415336203414328683660367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34215126418209752979521957 6415336203414328683660367)
        ·
          refine ⟨9623004305121493025490551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6415336203414328683660367 9623004305121493025490551)
          ·
            refine ⟨14434506457682239538235827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9623004305121493025490551 14434506457682239538235827)
            ·
              refine ⟨21651759686523359307353741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14434506457682239538235827 21651759686523359307353741)
              ·
                refine ⟨8119409882446259740257653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21651759686523359307353741 8119409882446259740257653)
                ·
                  refine ⟨761194676479336850649155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8119409882446259740257653 761194676479336850649155)
                  ·
                    refine ⟨1141792014719005275973733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 761194676479336850649155 1141792014719005275973733)
                    ·
                      refine ⟨214086002759813489245075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1141792014719005275973733 214086002759813489245075)
                      ·
                        rfl

theorem cell23_416931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_416931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_416931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_416931 prefixEnd_416931 := by exact prefixLift 416931
  have htrace : WordTrace (prefixWord ++ tailWord_416931) baseStart_416931 baseEnd_416931 := by
    simpa [prefixWord, tailWord_416931, baseEnd_416931] using wordTrace_append hprefix tailTrace_416931
  have hstable : (prefixWord ++ tailWord_416931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416931).length < 2 ^ (prefixWord ++ tailWord_416931).sum := by decide
  have hdescent : baseEnd_416931 < baseStart_416931 := by decide
  rcases family_descends (prefixWord ++ tailWord_416931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416935 : List Nat := [1, 1, 6, 2, 1, 1, 1, 2, 1, 5, 2]
def baseStart_416935 : Nat := 118140960795 + 416935 * 2 ^ 59
def prefixEnd_416935 : Nat := 4983230072969 + 3 ^ 40 * 416935 * 2
def baseEnd_416935 : Nat := 214088056682431473595057

theorem tailTrace_416935 : CollatzResearch.WordTrace tailWord_416935 prefixEnd_416935 214088056682431473595057 := by
  unfold tailWord_416935
  simp only [CollatzResearch.WordTrace]
  refine ⟨15206868744523176674044259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10137912496348784449362839 15206868744523176674044259)
  ·
    refine ⟨22810303116784765011066389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15206868744523176674044259 22810303116784765011066389)
    ·
      refine ⟨1069232958599285859893737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22810303116784765011066389 1069232958599285859893737)
      ·
        refine ⟨801924718949464394920303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1069232958599285859893737 801924718949464394920303)
        ·
          refine ⟨1202887078424196592380455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 801924718949464394920303 1202887078424196592380455)
          ·
            refine ⟨1804330617636294888570683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1202887078424196592380455 1804330617636294888570683)
            ·
              refine ⟨2706495926454442332856025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1804330617636294888570683 2706495926454442332856025)
              ·
                refine ⟨2029871944840831749642019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2706495926454442332856025 2029871944840831749642019)
                ·
                  refine ⟨3044807917261247624463029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2029871944840831749642019 3044807917261247624463029)
                  ·
                    refine ⟨285450742243241964793409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3044807917261247624463029 285450742243241964793409)
                    ·
                      refine ⟨214088056682431473595057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 285450742243241964793409 214088056682431473595057)
                      ·
                        rfl

theorem cell23_416935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_416935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_416935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_416935 prefixEnd_416935 := by exact prefixLift 416935
  have htrace : WordTrace (prefixWord ++ tailWord_416935) baseStart_416935 baseEnd_416935 := by
    simpa [prefixWord, tailWord_416935, baseEnd_416935] using wordTrace_append hprefix tailTrace_416935
  have hstable : (prefixWord ++ tailWord_416935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416935).length < 2 ^ (prefixWord ++ tailWord_416935).sum := by decide
  have hdescent : baseEnd_416935 < baseStart_416935 := by decide
  rcases family_descends (prefixWord ++ tailWord_416935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416945 : List Nat := [1, 2, 2, 5, 1, 2, 2, 2, 1, 5]
def baseStart_416945 : Nat := 118140960795 + 416945 * 2 ^ 59
def prefixEnd_416945 : Nat := 4983230072969 + 3 ^ 40 * 416945 * 2
def baseEnd_416945 : Nat := 71364397162992144823337

theorem tailTrace_416945 : CollatzResearch.WordTrace tailWord_416945 prefixEnd_416945 71364397162992144823337 := by
  unfold tailWord_416945
  simp only [CollatzResearch.WordTrace]
  refine ⟨15207233474486948381908289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10138155649657965587938859 15207233474486948381908289)
  ·
    refine ⟨11405425105865211286431217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15207233474486948381908289 11405425105865211286431217)
    ·
      refine ⟨8554068829398908464823413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11405425105865211286431217 8554068829398908464823413)
      ·
        refine ⟨801943952756147668577195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8554068829398908464823413 801943952756147668577195)
        ·
          refine ⟨1202915929134221502865793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 801943952756147668577195 1202915929134221502865793)
          ·
            refine ⟨902186946850666127149345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1202915929134221502865793 902186946850666127149345)
            ·
              refine ⟨676640210137999595362009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 902186946850666127149345 676640210137999595362009)
              ·
                refine ⟨507480157603499696521507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 676640210137999595362009 507480157603499696521507)
                ·
                  refine ⟨761220236405249544782261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 507480157603499696521507 761220236405249544782261)
                  ·
                    refine ⟨71364397162992144823337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 761220236405249544782261 71364397162992144823337)
                    ·
                      rfl

theorem cell23_416945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 2, 1, 5].length) (baseStart_416945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_416945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_416945 prefixEnd_416945 := by exact prefixLift 416945
  have htrace : WordTrace (prefixWord ++ tailWord_416945) baseStart_416945 baseEnd_416945 := by
    simpa [prefixWord, tailWord_416945, baseEnd_416945] using wordTrace_append hprefix tailTrace_416945
  have hstable : (prefixWord ++ tailWord_416945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416945).length < 2 ^ (prefixWord ++ tailWord_416945).sum := by decide
  have hdescent : baseEnd_416945 < baseStart_416945 := by decide
  rcases family_descends (prefixWord ++ tailWord_416945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416951 : List Nat := [1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 5]
def baseStart_416951 : Nat := 118140960795 + 416951 * 2 ^ 59
def prefixEnd_416951 : Nat := 4983230072969 + 3 ^ 40 * 416951 * 2
def baseEnd_416951 : Nat := 214096272372903410994983

theorem tailTrace_416951 : CollatzResearch.WordTrace tailWord_416951 prefixEnd_416951 214096272372903410994983 := by
  unfold tailWord_416951
  simp only [CollatzResearch.WordTrace]
  refine ⟨15207452312465211406626707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10138301541643474271084471 15207452312465211406626707)
  ·
    refine ⟨22811178468697817109940061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15207452312465211406626707 22811178468697817109940061)
    ·
      refine ⟨8554191925761681416227523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22811178468697817109940061 8554191925761681416227523)
      ·
        refine ⟨12831287888642522124341285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8554191925761681416227523 12831287888642522124341285)
        ·
          refine ⟨2405866479120472898313991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12831287888642522124341285 2405866479120472898313991)
          ·
            refine ⟨3608799718680709347470987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2405866479120472898313991 3608799718680709347470987)
            ·
              refine ⟨5413199578021064021206481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3608799718680709347470987 5413199578021064021206481)
              ·
                refine ⟨4059899683515798015904861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5413199578021064021206481 4059899683515798015904861)
                ·
                  refine ⟨1522462381318424255964323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4059899683515798015904861 1522462381318424255964323)
                  ·
                    refine ⟨2283693571977636383946485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1522462381318424255964323 2283693571977636383946485)
                    ·
                      refine ⟨214096272372903410994983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2283693571977636383946485 214096272372903410994983)
                      ·
                        rfl

theorem cell23_416951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 5].length) (baseStart_416951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_416951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_416951 prefixEnd_416951 := by exact prefixLift 416951
  have htrace : WordTrace (prefixWord ++ tailWord_416951) baseStart_416951 baseEnd_416951 := by
    simpa [prefixWord, tailWord_416951, baseEnd_416951] using wordTrace_append hprefix tailTrace_416951
  have hstable : (prefixWord ++ tailWord_416951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416951).length < 2 ^ (prefixWord ++ tailWord_416951).sum := by decide
  have hdescent : baseEnd_416951 < baseStart_416951 := by decide
  rcases family_descends (prefixWord ++ tailWord_416951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416992 : List Nat := [2, 1, 1, 3, 1, 6, 2, 1, 2, 4]
def baseStart_416992 : Nat := 118140960795 + 416992 * 2 ^ 59
def prefixEnd_416992 : Nat := 4983230072969 + 3 ^ 40 * 416992 * 2
def baseEnd_416992 : Nat := 71372441693245916860765

theorem tailTrace_416992 : CollatzResearch.WordTrace tailWord_416992 prefixEnd_416992 71372441693245916860765 := by
  unfold tailWord_416992
  simp only [CollatzResearch.WordTrace]
  refine ⟨7604473852658337704434615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10139298470211116939246153 7604473852658337704434615)
  ·
    refine ⟨11406710778987506556651923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7604473852658337704434615 11406710778987506556651923)
    ·
      refine ⟨17110066168481259834977885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11406710778987506556651923 17110066168481259834977885)
      ·
        refine ⟨6416274813180472438116707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17110066168481259834977885 6416274813180472438116707)
        ·
          refine ⟨9624412219770708657175061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6416274813180472438116707 9624412219770708657175061)
          ·
            refine ⟨451144322801751968305081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9624412219770708657175061 451144322801751968305081)
            ·
              refine ⟨338358242101313976228811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 451144322801751968305081 338358242101313976228811)
              ·
                refine ⟨507537363151970964343217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 338358242101313976228811 507537363151970964343217)
                ·
                  refine ⟨380653022363978223257413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 507537363151970964343217 380653022363978223257413)
                  ·
                    refine ⟨71372441693245916860765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 380653022363978223257413 71372441693245916860765)
                    ·
                      rfl

theorem cell23_416992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 2, 4].length) (baseStart_416992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_416992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_416992 prefixEnd_416992 := by exact prefixLift 416992
  have htrace : WordTrace (prefixWord ++ tailWord_416992) baseStart_416992 baseEnd_416992 := by
    simpa [prefixWord, tailWord_416992, baseEnd_416992] using wordTrace_append hprefix tailTrace_416992
  have hstable : (prefixWord ++ tailWord_416992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416992).length < 2 ^ (prefixWord ++ tailWord_416992).sum := by decide
  have hdescent : baseEnd_416992 < baseStart_416992 := by decide
  rcases family_descends (prefixWord ++ tailWord_416992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416999 : List Nat := [1, 1, 5, 3, 3, 1, 1, 2, 1, 1, 4]
def baseStart_416999 : Nat := 118140960795 + 416999 * 2 ^ 59
def prefixEnd_416999 : Nat := 4983230072969 + 3 ^ 40 * 416999 * 2
def baseEnd_416999 : Nat := 214120919444319223194763

theorem tailTrace_416999 : CollatzResearch.WordTrace tailWord_416999 prefixEnd_416999 214120919444319223194763 := by
  unfold tailWord_416999
  simp only [CollatzResearch.WordTrace]
  refine ⟨15209203016291315604374051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10139468677527543736249367 15209203016291315604374051)
  ·
    refine ⟨22813804524436973406561077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15209203016291315604374051 22813804524436973406561077)
    ·
      refine ⟨2138794174165966256865101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22813804524436973406561077 2138794174165966256865101)
      ·
        refine ⟨802047815312237346324413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2138794174165966256865101 802047815312237346324413)
        ·
          refine ⟨300767930742089004871655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 802047815312237346324413 300767930742089004871655)
          ·
            refine ⟨451151896113133507307483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300767930742089004871655 451151896113133507307483)
            ·
              refine ⟨676727844169700260961225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 451151896113133507307483 676727844169700260961225)
              ·
                refine ⟨507545883127275195720919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 676727844169700260961225 507545883127275195720919)
                ·
                  refine ⟨761318824690912793581379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 507545883127275195720919 761318824690912793581379)
                  ·
                    refine ⟨1141978237036369190372069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 761318824690912793581379 1141978237036369190372069)
                    ·
                      refine ⟨214120919444319223194763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1141978237036369190372069 214120919444319223194763)
                      ·
                        rfl

theorem cell23_416999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_416999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_416999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_416999 prefixEnd_416999 := by exact prefixLift 416999
  have htrace : WordTrace (prefixWord ++ tailWord_416999) baseStart_416999 baseEnd_416999 := by
    simpa [prefixWord, tailWord_416999, baseEnd_416999] using wordTrace_append hprefix tailTrace_416999
  have hstable : (prefixWord ++ tailWord_416999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416999).length < 2 ^ (prefixWord ++ tailWord_416999).sum := by decide
  have hdescent : baseEnd_416999 < baseStart_416999 := by decide
  rcases family_descends (prefixWord ++ tailWord_416999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417002 : List Nat := [3, 1, 3, 1, 1, 5, 1, 2, 1, 2, 3]
def baseStart_417002 : Nat := 118140960795 + 417002 * 2 ^ 59
def prefixEnd_417002 : Nat := 4983230072969 + 3 ^ 40 * 417002 * 2
def baseEnd_417002 : Nat := 214122459886282711457249

theorem tailTrace_417002 : CollatzResearch.WordTrace tailWord_417002 prefixEnd_417002 214122459886282711457249 := by
  unfold tailWord_417002
  simp only [CollatzResearch.WordTrace]
  refine ⟨3802328108820111779183315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10139541623520298077822173 3802328108820111779183315)
  ·
    refine ⟨5703492163230167668774973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3802328108820111779183315 5703492163230167668774973)
    ·
      refine ⟨2138809561211312875790615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5703492163230167668774973 2138809561211312875790615)
      ·
        refine ⟨3208214341816969313685923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2138809561211312875790615 3208214341816969313685923)
        ·
          refine ⟨4812321512725453970528885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3208214341816969313685923 4812321512725453970528885)
          ·
            refine ⟨451155141818011309737083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4812321512725453970528885 451155141818011309737083)
            ·
              refine ⟨676732712727016964605625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 451155141818011309737083 676732712727016964605625)
              ·
                refine ⟨507549534545262723454219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 676732712727016964605625 507549534545262723454219)
                ·
                  refine ⟨761324301817894085181329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 507549534545262723454219 761324301817894085181329)
                  ·
                    refine ⟨570993226363420563885997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 761324301817894085181329 570993226363420563885997)
                    ·
                      refine ⟨214122459886282711457249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 570993226363420563885997 214122459886282711457249)
                      ·
                        rfl

theorem cell23_417002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_417002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417002 prefixEnd_417002 := by exact prefixLift 417002
  have htrace : WordTrace (prefixWord ++ tailWord_417002) baseStart_417002 baseEnd_417002 := by
    simpa [prefixWord, tailWord_417002, baseEnd_417002] using wordTrace_append hprefix tailTrace_417002
  have hstable : (prefixWord ++ tailWord_417002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417002).length < 2 ^ (prefixWord ++ tailWord_417002).sum := by decide
  have hdescent : baseEnd_417002 < baseStart_417002 := by decide
  rcases family_descends (prefixWord ++ tailWord_417002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417038 : List Nat := [4, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4]
def baseStart_417038 : Nat := 118140960795 + 417038 * 2 ^ 59
def prefixEnd_417038 : Nat := 4983230072969 + 3 ^ 40 * 417038 * 2
def baseEnd_417038 : Nat := 214140945189844570607083

theorem tailTrace_417038 : CollatzResearch.WordTrace tailWord_417038 prefixEnd_417038 214140945189844570607083 := by
  unfold tailWord_417038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1901328182893753158130471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10140416975433350176695845 1901328182893753158130471)
  ·
    refine ⟨2851992274340629737195707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1901328182893753158130471 2851992274340629737195707)
    ·
      refine ⟨4277988411510944605793561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2851992274340629737195707 4277988411510944605793561)
      ·
        refine ⟨3208491308633208454345171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4277988411510944605793561 3208491308633208454345171)
        ·
          refine ⟨4812736962949812681517757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3208491308633208454345171 4812736962949812681517757)
          ·
            refine ⟨1804776361106179755569159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4812736962949812681517757 1804776361106179755569159)
            ·
              refine ⟨2707164541659269633353739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1804776361106179755569159 2707164541659269633353739)
              ·
                refine ⟨4060746812488904450030609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2707164541659269633353739 4060746812488904450030609)
                ·
                  refine ⟨3045560109366678337522957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4060746812488904450030609 3045560109366678337522957)
                  ·
                    refine ⟨1142085041012504376571109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3045560109366678337522957 1142085041012504376571109)
                    ·
                      refine ⟨214140945189844570607083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1142085041012504376571109 214140945189844570607083)
                      ·
                        rfl

theorem cell23_417038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_417038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417038 prefixEnd_417038 := by exact prefixLift 417038
  have htrace : WordTrace (prefixWord ++ tailWord_417038) baseStart_417038 baseEnd_417038 := by
    simpa [prefixWord, tailWord_417038, baseEnd_417038] using wordTrace_append hprefix tailTrace_417038
  have hstable : (prefixWord ++ tailWord_417038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417038).length < 2 ^ (prefixWord ++ tailWord_417038).sum := by decide
  have hdescent : baseEnd_417038 < baseStart_417038 := by decide
  rcases family_descends (prefixWord ++ tailWord_417038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417048 : List Nat := [2, 1, 2, 3, 1, 4, 1, 1, 2, 6]
def baseStart_417048 : Nat := 118140960795 + 417048 * 2 ^ 59
def prefixEnd_417048 : Nat := 4983230072969 + 3 ^ 40 * 417048 * 2
def baseEnd_417048 : Nat := 71382026665463177160679

theorem tailTrace_417048 : CollatzResearch.WordTrace tailWord_417048 prefixEnd_417048 71382026665463177160679 := by
  unfold tailWord_417048
  simp only [CollatzResearch.WordTrace]
  refine ⟨7605495096556898486453899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10140660128742531315271865 7605495096556898486453899)
  ·
    refine ⟨11408242644835347729680849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7605495096556898486453899 11408242644835347729680849)
    ·
      refine ⟨8556181983626510797260637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11408242644835347729680849 8556181983626510797260637)
      ·
        refine ⟨3208568243859941548972739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8556181983626510797260637 3208568243859941548972739)
        ·
          refine ⟨4812852365789912323459109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3208568243859941548972739 4812852365789912323459109)
          ·
            refine ⟨902409818585608560648583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4812852365789912323459109 902409818585608560648583)
            ·
              refine ⟨1353614727878412840972875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 902409818585608560648583 1353614727878412840972875)
              ·
                refine ⟨2030422091817619261459313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1353614727878412840972875 2030422091817619261459313)
                ·
                  refine ⟨1522816568863214446094485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2030422091817619261459313 1522816568863214446094485)
                  ·
                    refine ⟨71382026665463177160679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1522816568863214446094485 71382026665463177160679)
                    ·
                      rfl

theorem cell23_417048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 2, 6].length) (baseStart_417048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417048 prefixEnd_417048 := by exact prefixLift 417048
  have htrace : WordTrace (prefixWord ++ tailWord_417048) baseStart_417048 baseEnd_417048 := by
    simpa [prefixWord, tailWord_417048, baseEnd_417048] using wordTrace_append hprefix tailTrace_417048
  have hstable : (prefixWord ++ tailWord_417048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417048).length < 2 ^ (prefixWord ++ tailWord_417048).sum := by decide
  have hdescent : baseEnd_417048 < baseStart_417048 := by decide
  rcases family_descends (prefixWord ++ tailWord_417048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417071 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 7]
def baseStart_417071 : Nat := 118140960795 + 417071 * 2 ^ 59
def prefixEnd_417071 : Nat := 4983230072969 + 3 ^ 40 * 417071 * 2
def baseEnd_417071 : Nat := 214157890051442941494431

theorem tailTrace_417071 : CollatzResearch.WordTrace tailWord_417071 prefixEnd_417071 214157890051442941494431 := by
  unfold tailWord_417071
  simp only [CollatzResearch.WordTrace]
  refine ⟨15211829072030471900995067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10141219381353647933996711 15211829072030471900995067)
  ·
    refine ⟨22817743608045707851492601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15211829072030471900995067 22817743608045707851492601)
    ·
      refine ⟨17113307706034280888619451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22817743608045707851492601 17113307706034280888619451)
      ·
        refine ⟨25669961559051421332929177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17113307706034280888619451 25669961559051421332929177)
        ·
          refine ⟨19252471169288565999696883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25669961559051421332929177 19252471169288565999696883)
          ·
            refine ⟨28878706753932848999545325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19252471169288565999696883 28878706753932848999545325)
            ·
              refine ⟨10829515032724818374829497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28878706753932848999545325 10829515032724818374829497)
              ·
                refine ⟨8122136274543613781122123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10829515032724818374829497 8122136274543613781122123)
                ·
                  refine ⟨12183204411815420671683185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8122136274543613781122123 12183204411815420671683185)
                  ·
                    refine ⟨9137403308861565503762389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12183204411815420671683185 9137403308861565503762389)
                    ·
                      refine ⟨214157890051442941494431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 9137403308861565503762389 214157890051442941494431)
                      ·
                        rfl

theorem cell23_417071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 7].length) (baseStart_417071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417071 prefixEnd_417071 := by exact prefixLift 417071
  have htrace : WordTrace (prefixWord ++ tailWord_417071) baseStart_417071 baseEnd_417071 := by
    simpa [prefixWord, tailWord_417071, baseEnd_417071] using wordTrace_append hprefix tailTrace_417071
  have hstable : (prefixWord ++ tailWord_417071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417071).length < 2 ^ (prefixWord ++ tailWord_417071).sum := by decide
  have hdescent : baseEnd_417071 < baseStart_417071 := by decide
  rcases family_descends (prefixWord ++ tailWord_417071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417088 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 3]
def baseStart_417088 : Nat := 118140960795 + 417088 * 2 ^ 59
def prefixEnd_417088 : Nat := 4983230072969 + 3 ^ 40 * 417088 * 2
def baseEnd_417088 : Nat := 214166619222569374981853

theorem tailTrace_417088 : CollatzResearch.WordTrace tailWord_417088 prefixEnd_417088 214166619222569374981853 := by
  unfold tailWord_417088
  simp only [CollatzResearch.WordTrace]
  refine ⟨7606224556484441902181959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10141632741979255869575945 7606224556484441902181959)
  ·
    refine ⟨11409336834726662853272939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7606224556484441902181959 11409336834726662853272939)
    ·
      refine ⟨17114005252089994279909409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11409336834726662853272939 17114005252089994279909409)
      ·
        refine ⟨12835503939067495709932057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17114005252089994279909409 12835503939067495709932057)
        ·
          refine ⟨9626627954300621782449043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12835503939067495709932057 9626627954300621782449043)
          ·
            refine ⟨14439941931450932673673565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9626627954300621782449043 14439941931450932673673565)
            ·
              refine ⟨5414978224294099752627587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14439941931450932673673565 5414978224294099752627587)
              ·
                refine ⟨8122467336441149628941381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5414978224294099752627587 8122467336441149628941381)
                ·
                  refine ⟨1522962625582715555426509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8122467336441149628941381 1522962625582715555426509)
                  ·
                    refine ⟨571110984593518333284941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1522962625582715555426509 571110984593518333284941)
                    ·
                      refine ⟨214166619222569374981853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 571110984593518333284941 214166619222569374981853)
                      ·
                        rfl

theorem cell23_417088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 3].length) (baseStart_417088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417088 prefixEnd_417088 := by exact prefixLift 417088
  have htrace : WordTrace (prefixWord ++ tailWord_417088) baseStart_417088 baseEnd_417088 := by
    simpa [prefixWord, tailWord_417088, baseEnd_417088] using wordTrace_append hprefix tailTrace_417088
  have hstable : (prefixWord ++ tailWord_417088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417088).length < 2 ^ (prefixWord ++ tailWord_417088).sum := by decide
  have hdescent : baseEnd_417088 < baseStart_417088 := by decide
  rcases family_descends (prefixWord ++ tailWord_417088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417089 : List Nat := [1, 2, 5, 2, 1, 2, 1, 1, 4, 2, 2]
def baseStart_417089 : Nat := 118140960795 + 417089 * 2 ^ 59
def prefixEnd_417089 : Nat := 4983230072969 + 3 ^ 40 * 417089 * 2
def baseEnd_417089 : Nat := 214167132703223871069349

theorem tailTrace_417089 : CollatzResearch.WordTrace tailWord_417089 prefixEnd_417089 214167132703223871069349 := by
  unfold tailWord_417089
  simp only [CollatzResearch.WordTrace]
  refine ⟨15212485585965260975150321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10141657057310173983433547 15212485585965260975150321)
  ·
    refine ⟨11409364189473945731362741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15212485585965260975150321 11409364189473945731362741)
    ·
      refine ⟨1069627892763182412315257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11409364189473945731362741 1069627892763182412315257)
      ·
        refine ⟨802220919572386809236443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1069627892763182412315257 802220919572386809236443)
        ·
          refine ⟨1203331379358580213854665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 802220919572386809236443 1203331379358580213854665)
          ·
            refine ⟨902498534518935160390999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1203331379358580213854665 902498534518935160390999)
            ·
              refine ⟨1353747801778402740586499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 902498534518935160390999 1353747801778402740586499)
              ·
                refine ⟨2030621702667604110879749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1353747801778402740586499 2030621702667604110879749)
                ·
                  refine ⟨380741569250175770789953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2030621702667604110879749 380741569250175770789953)
                  ·
                    refine ⟨285556176937631828092465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 380741569250175770789953 285556176937631828092465)
                    ·
                      refine ⟨214167132703223871069349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 285556176937631828092465 214167132703223871069349)
                      ·
                        rfl

theorem cell23_417089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_417089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417089 prefixEnd_417089 := by exact prefixLift 417089
  have htrace : WordTrace (prefixWord ++ tailWord_417089) baseStart_417089 baseEnd_417089 := by
    simpa [prefixWord, tailWord_417089, baseEnd_417089] using wordTrace_append hprefix tailTrace_417089
  have hstable : (prefixWord ++ tailWord_417089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417089).length < 2 ^ (prefixWord ++ tailWord_417089).sum := by decide
  have hdescent : baseEnd_417089 < baseStart_417089 := by decide
  rcases family_descends (prefixWord ++ tailWord_417089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417095 : List Nat := [1, 1, 4, 1, 2, 3, 2, 4, 5]
def baseStart_417095 : Nat := 118140960795 + 417095 * 2 ^ 59
def prefixEnd_417095 : Nat := 4983230072969 + 3 ^ 40 * 417095 * 2
def baseEnd_417095 : Nat := 23796690398572316399369

theorem tailTrace_417095 : CollatzResearch.WordTrace tailWord_417095 prefixEnd_417095 23796690398572316399369 := by
  unfold tailWord_417095
  simp only [CollatzResearch.WordTrace]
  refine ⟨15212704423943523999868739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10141802949295682666579159 15212704423943523999868739)
  ·
    refine ⟨22819056635915285999803109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15212704423943523999868739 22819056635915285999803109)
    ·
      refine ⟨4278573119234116124963083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22819056635915285999803109 4278573119234116124963083)
      ·
        refine ⟨6417859678851174187444625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4278573119234116124963083 6417859678851174187444625)
        ·
          refine ⟨4813394759138380640583469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6417859678851174187444625 4813394759138380640583469)
          ·
            refine ⟨1805023034676892740218801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4813394759138380640583469 1805023034676892740218801)
            ·
              refine ⟨1353767276007669555164101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1805023034676892740218801 1353767276007669555164101)
              ·
                refine ⟨253831364251438041593269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1353767276007669555164101 253831364251438041593269)
                ·
                  refine ⟨23796690398572316399369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 253831364251438041593269 23796690398572316399369)
                  ·
                    rfl

theorem cell23_417095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 4, 5].length) (baseStart_417095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417095 prefixEnd_417095 := by exact prefixLift 417095
  have htrace : WordTrace (prefixWord ++ tailWord_417095) baseStart_417095 baseEnd_417095 := by
    simpa [prefixWord, tailWord_417095, baseEnd_417095] using wordTrace_append hprefix tailTrace_417095
  have hstable : (prefixWord ++ tailWord_417095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417095).length < 2 ^ (prefixWord ++ tailWord_417095).sum := by decide
  have hdescent : baseEnd_417095 < baseStart_417095 := by decide
  rcases family_descends (prefixWord ++ tailWord_417095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417108 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 3, 7]
def baseStart_417108 : Nat := 118140960795 + 417108 * 2 ^ 59
def prefixEnd_417108 : Nat := 4983230072969 + 3 ^ 40 * 417108 * 2
def baseEnd_417108 : Nat := 71392296278553098910587

theorem tailTrace_417108 : CollatzResearch.WordTrace tailWord_417108 prefixEnd_417108 71392296278553098910587 := by
  unfold tailWord_417108
  simp only [CollatzResearch.WordTrace]
  refine ⟨7606589286448213610045989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10142119048597618146727985 7606589286448213610045989)
  ·
    refine ⟨1426235491209040051883623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7606589286448213610045989 1426235491209040051883623)
    ·
      refine ⟨2139353236813560077825435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1426235491209040051883623 2139353236813560077825435)
      ·
        refine ⟨3209029855220340116738153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2139353236813560077825435 3209029855220340116738153)
        ·
          refine ⟨2406772391415255087553615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3209029855220340116738153 2406772391415255087553615)
          ·
            refine ⟨3610158587122882631330423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2406772391415255087553615 3610158587122882631330423)
            ·
              refine ⟨5415237880684323946995635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3610158587122882631330423 5415237880684323946995635)
              ·
                refine ⟨8122856821026485920493453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5415237880684323946995635 8122856821026485920493453)
                ·
                  refine ⟨3046071307884932220185045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8122856821026485920493453 3046071307884932220185045)
                  ·
                    refine ⟨71392296278553098910587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3046071307884932220185045 71392296278553098910587)
                    ·
                      rfl

theorem cell23_417108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_417108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417108 prefixEnd_417108 := by exact prefixLift 417108
  have htrace : WordTrace (prefixWord ++ tailWord_417108) baseStart_417108 baseEnd_417108 := by
    simpa [prefixWord, tailWord_417108, baseEnd_417108] using wordTrace_append hprefix tailTrace_417108
  have hstable : (prefixWord ++ tailWord_417108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417108).length < 2 ^ (prefixWord ++ tailWord_417108).sum := by decide
  have hdescent : baseEnd_417108 < baseStart_417108 := by decide
  rcases family_descends (prefixWord ++ tailWord_417108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417110 : List Nat := [5, 2, 3, 1, 1, 1, 2, 2, 1, 3, 2]
def baseStart_417110 : Nat := 118140960795 + 417110 * 2 ^ 59
def prefixEnd_417110 : Nat := 4983230072969 + 3 ^ 40 * 417110 * 2
def baseEnd_417110 : Nat := 214177915796968288906753

theorem tailTrace_417110 : CollatzResearch.WordTrace tailWord_417110 prefixEnd_417110 214177915796968288906753 := by
  unfold tailWord_417110
  simp only [CollatzResearch.WordTrace]
  refine ⟨950828219930573847604049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10142167679259454374443189 950828219930573847604049)
  ·
    refine ⟨713121164947930385703037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 950828219930573847604049 713121164947930385703037)
    ·
      refine ⟨267420436855473894638639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 713121164947930385703037 267420436855473894638639)
      ·
        refine ⟨401130655283210841957959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267420436855473894638639 401130655283210841957959)
        ·
          refine ⟨601695982924816262936939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401130655283210841957959 601695982924816262936939)
          ·
            refine ⟨902543974387224394405409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 601695982924816262936939 902543974387224394405409)
            ·
              refine ⟨676907980790418295804057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 902543974387224394405409 676907980790418295804057)
              ·
                refine ⟨507680985592813721853043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 676907980790418295804057 507680985592813721853043)
                ·
                  refine ⟨761521478389220582779565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 507680985592813721853043 761521478389220582779565)
                  ·
                    refine ⟨285570554395957718542337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 761521478389220582779565 285570554395957718542337)
                    ·
                      refine ⟨214177915796968288906753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 285570554395957718542337 214177915796968288906753)
                      ·
                        rfl

theorem cell23_417110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_417110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417110 prefixEnd_417110 := by exact prefixLift 417110
  have htrace : WordTrace (prefixWord ++ tailWord_417110) baseStart_417110 baseEnd_417110 := by
    simpa [prefixWord, tailWord_417110, baseEnd_417110] using wordTrace_append hprefix tailTrace_417110
  have hstable : (prefixWord ++ tailWord_417110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417110).length < 2 ^ (prefixWord ++ tailWord_417110).sum := by decide
  have hdescent : baseEnd_417110 < baseStart_417110 := by decide
  rcases family_descends (prefixWord ++ tailWord_417110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417145 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 4, 4, 2]
def baseStart_417145 : Nat := 118140960795 + 417145 * 2 ^ 59
def prefixEnd_417145 : Nat := 4983230072969 + 3 ^ 40 * 417145 * 2
def baseEnd_417145 : Nat := 214195887619875651969091

theorem tailTrace_417145 : CollatzResearch.WordTrace tailWord_417145 prefixEnd_417145 214195887619875651969091 := by
  unfold tailWord_417145
  simp only [CollatzResearch.WordTrace]
  refine ⟨15214528073762382539188889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10143018715841588359459259 15214528073762382539188889)
  ·
    refine ⟨11410896055321786904391667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15214528073762382539188889 11410896055321786904391667)
    ·
      refine ⟨17116344082982680356587501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11410896055321786904391667 17116344082982680356587501)
      ·
        refine ⟨6418629031118505133720313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17116344082982680356587501 6418629031118505133720313)
        ·
          refine ⟨4813971773338878850290235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6418629031118505133720313 4813971773338878850290235)
          ·
            refine ⟨7220957660008318275435353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4813971773338878850290235 7220957660008318275435353)
            ·
              refine ⟨5415718245006238706576515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7220957660008318275435353 5415718245006238706576515)
              ·
                refine ⟨8123577367509358059864773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5415718245006238706576515 8123577367509358059864773)
                ·
                  refine ⟨1523170756408004636224645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8123577367509358059864773 1523170756408004636224645)
                  ·
                    refine ⟨285594516826500869292121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1523170756408004636224645 285594516826500869292121)
                    ·
                      refine ⟨214195887619875651969091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 285594516826500869292121 214195887619875651969091)
                      ·
                        rfl

theorem cell23_417145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 4, 2].length) (baseStart_417145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417145 prefixEnd_417145 := by exact prefixLift 417145
  have htrace : WordTrace (prefixWord ++ tailWord_417145) baseStart_417145 baseEnd_417145 := by
    simpa [prefixWord, tailWord_417145, baseEnd_417145] using wordTrace_append hprefix tailTrace_417145
  have hstable : (prefixWord ++ tailWord_417145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417145).length < 2 ^ (prefixWord ++ tailWord_417145).sum := by decide
  have hdescent : baseEnd_417145 < baseStart_417145 := by decide
  rcases family_descends (prefixWord ++ tailWord_417145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417188 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 1, 1, 8]
def baseStart_417188 : Nat := 118140960795 + 417188 * 2 ^ 59
def prefixEnd_417188 : Nat := 4983230072969 + 3 ^ 40 * 417188 * 2
def baseEnd_417188 : Nat := 214217967288018983731393

theorem tailTrace_417188 : CollatzResearch.WordTrace tailWord_417188 prefixEnd_417188 214217967288018983731393 := by
  unfold tailWord_417188
  simp only [CollatzResearch.WordTrace]
  refine ⟨7608048206303300441502109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10144064275071067255336145 7608048206303300441502109)
  ·
    refine ⟨2853018077363737665563291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7608048206303300441502109 2853018077363737665563291)
    ·
      refine ⟨4279527116045606498344937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2853018077363737665563291 4279527116045606498344937)
      ·
        refine ⟨3209645337034204873758703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4279527116045606498344937 3209645337034204873758703)
        ·
          refine ⟨4814468005551307310638055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3209645337034204873758703 4814468005551307310638055)
          ·
            refine ⟨7221702008326960965957083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4814468005551307310638055 7221702008326960965957083)
            ·
              refine ⟨10832553012490441448935625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7221702008326960965957083 10832553012490441448935625)
              ·
                refine ⟨8124414759367831086701719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10832553012490441448935625 8124414759367831086701719)
                ·
                  refine ⟨12186622139051746630052579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8124414759367831086701719 12186622139051746630052579)
                  ·
                    refine ⟨18279933208577619945078869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12186622139051746630052579 18279933208577619945078869)
                    ·
                      refine ⟨214217967288018983731393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 18279933208577619945078869 214217967288018983731393)
                      ·
                        rfl

theorem cell23_417188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_417188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417188 prefixEnd_417188 := by exact prefixLift 417188
  have htrace : WordTrace (prefixWord ++ tailWord_417188) baseStart_417188 baseEnd_417188 := by
    simpa [prefixWord, tailWord_417188, baseEnd_417188] using wordTrace_append hprefix tailTrace_417188
  have hstable : (prefixWord ++ tailWord_417188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417188).length < 2 ^ (prefixWord ++ tailWord_417188).sum := by decide
  have hdescent : baseEnd_417188 < baseStart_417188 := by decide
  rcases family_descends (prefixWord ++ tailWord_417188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417249 : List Nat := [1, 2, 3, 1, 2, 5, 2, 1, 1, 5]
def baseStart_417249 : Nat := 118140960795 + 417249 * 2 ^ 59
def prefixEnd_417249 : Nat := 4983230072969 + 3 ^ 40 * 417249 * 2
def baseEnd_417249 : Nat := 71416429869314415022871

theorem tailTrace_417249 : CollatzResearch.WordTrace tailWord_417249 prefixEnd_417249 71416429869314415022871 := by
  unfold tailWord_417249
  simp only [CollatzResearch.WordTrace]
  refine ⟨15218321265385608300974801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10145547510257072200649867 15218321265385608300974801)
  ·
    refine ⟨11413740949039206225731101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15218321265385608300974801 11413740949039206225731101)
    ·
      refine ⟨4280152855889702334649163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11413740949039206225731101 4280152855889702334649163)
      ·
        refine ⟨6420229283834553501973745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4280152855889702334649163 6420229283834553501973745)
        ·
          refine ⟨4815171962875915126480309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6420229283834553501973745 4815171962875915126480309)
          ·
            refine ⟨451422371519617043107529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4815171962875915126480309 451422371519617043107529)
            ·
              refine ⟨338566778639712782330647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 451422371519617043107529 338566778639712782330647)
              ·
                refine ⟨507850167959569173495971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 338566778639712782330647 507850167959569173495971)
                ·
                  refine ⟨761775251939353760243957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 507850167959569173495971 761775251939353760243957)
                  ·
                    refine ⟨71416429869314415022871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 761775251939353760243957 71416429869314415022871)
                    ·
                      rfl

theorem cell23_417249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 1, 1, 5].length) (baseStart_417249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417249 prefixEnd_417249 := by exact prefixLift 417249
  have htrace : WordTrace (prefixWord ++ tailWord_417249) baseStart_417249 baseEnd_417249 := by
    simpa [prefixWord, tailWord_417249, baseEnd_417249] using wordTrace_append hprefix tailTrace_417249
  have hstable : (prefixWord ++ tailWord_417249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417249).length < 2 ^ (prefixWord ++ tailWord_417249).sum := by decide
  have hdescent : baseEnd_417249 < baseStart_417249 := by decide
  rcases family_descends (prefixWord ++ tailWord_417249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417262 : List Nat := [4, 1, 2, 1, 2, 1, 3, 1, 4, 4]
def baseStart_417262 : Nat := 118140960795 + 417262 * 2 ^ 59
def prefixEnd_417262 : Nat := 4983230072969 + 3 ^ 40 * 417262 * 2
def baseEnd_417262 : Nat := 71418654952150564735351

theorem tailTrace_417262 : CollatzResearch.WordTrace tailWord_417262 prefixEnd_417262 71418654952150564735351 := by
  unfold tailWord_417262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1902349426792313940149755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10145863609559007680798693 1902349426792313940149755)
  ·
    refine ⟨2853524140188470910224633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1902349426792313940149755 2853524140188470910224633)
    ·
      refine ⟨2140143105141353182668475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2853524140188470910224633 2140143105141353182668475)
      ·
        refine ⟨3210214657712029774002713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2140143105141353182668475 3210214657712029774002713)
        ·
          refine ⟨2407660993284022330502035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3210214657712029774002713 2407660993284022330502035)
          ·
            refine ⟨3611491489926033495753053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2407660993284022330502035 3611491489926033495753053)
            ·
              refine ⟨1354309308722262560907395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3611491489926033495753053 1354309308722262560907395)
              ·
                refine ⟨2031463963083393841361093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1354309308722262560907395 2031463963083393841361093)
                ·
                  refine ⟨380899493078136345255205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2031463963083393841361093 380899493078136345255205)
                  ·
                    refine ⟨71418654952150564735351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 380899493078136345255205 71418654952150564735351)
                    ·
                      rfl

theorem cell23_417262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_417262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417262 prefixEnd_417262 := by exact prefixLift 417262
  have htrace : WordTrace (prefixWord ++ tailWord_417262) baseStart_417262 baseEnd_417262 := by
    simpa [prefixWord, tailWord_417262, baseEnd_417262] using wordTrace_append hprefix tailTrace_417262
  have hstable : (prefixWord ++ tailWord_417262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417262).length < 2 ^ (prefixWord ++ tailWord_417262).sum := by decide
  have hdescent : baseEnd_417262 < baseStart_417262 := by decide
  rcases family_descends (prefixWord ++ tailWord_417262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417320 : List Nat := [2, 1, 5, 2, 3, 1, 1, 1, 3, 2, 2]
def baseStart_417320 : Nat := 118140960795 + 417320 * 2 ^ 59
def prefixEnd_417320 : Nat := 4983230072969 + 3 ^ 40 * 417320 * 2
def baseEnd_417320 : Nat := 214285746734412467280787

theorem tailTrace_417320 : CollatzResearch.WordTrace tailWord_417320 prefixEnd_417320 214285746734412467280787 := by
  unfold tailWord_417320
  simp only [CollatzResearch.WordTrace]
  refine ⟨7610455424064193713404707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10147273898752258284539609 7610455424064193713404707)
  ·
    refine ⟨11415683136096290570107061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7610455424064193713404707 11415683136096290570107061)
    ·
      refine ⟨1070220294009027240947537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11415683136096290570107061 1070220294009027240947537)
      ·
        refine ⟨802665220506770430710653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1070220294009027240947537 802665220506770430710653)
        ·
          refine ⟨300999457690038911516495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 802665220506770430710653 300999457690038911516495)
          ·
            refine ⟨451499186535058367274743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300999457690038911516495 451499186535058367274743)
            ·
              refine ⟨677248779802587550912115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 451499186535058367274743 677248779802587550912115)
              ·
                refine ⟨1015873169703881326368173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 677248779802587550912115 1015873169703881326368173)
                ·
                  refine ⟨380952438638955497388065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1015873169703881326368173 380952438638955497388065)
                  ·
                    refine ⟨285714328979216623041049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 380952438638955497388065 285714328979216623041049)
                    ·
                      refine ⟨214285746734412467280787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 285714328979216623041049 214285746734412467280787)
                      ·
                        rfl

theorem cell23_417320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_417320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417320 prefixEnd_417320 := by exact prefixLift 417320
  have htrace : WordTrace (prefixWord ++ tailWord_417320) baseStart_417320 baseEnd_417320 := by
    simpa [prefixWord, tailWord_417320, baseEnd_417320] using wordTrace_append hprefix tailTrace_417320
  have hstable : (prefixWord ++ tailWord_417320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417320).length < 2 ^ (prefixWord ++ tailWord_417320).sum := by decide
  have hdescent : baseEnd_417320 < baseStart_417320 := by decide
  rcases family_descends (prefixWord ++ tailWord_417320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417336 : List Nat := [2, 1, 2, 1, 4, 2, 4, 1, 2, 1, 3]
def baseStart_417336 : Nat := 118140960795 + 417336 * 2 ^ 59
def prefixEnd_417336 : Nat := 4983230072969 + 3 ^ 40 * 417336 * 2
def baseEnd_417336 : Nat := 214293962424884404680713

theorem tailTrace_417336 : CollatzResearch.WordTrace tailWord_417336 prefixEnd_417336 214293962424884404680713 := by
  unfold tailWord_417336
  simp only [CollatzResearch.WordTrace]
  refine ⟨7610747208035211079695931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10147662944046948106261241 7610747208035211079695931)
  ·
    refine ⟨11416120812052816619543897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7610747208035211079695931 11416120812052816619543897)
    ·
      refine ⟨8562090609039612464657923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11416120812052816619543897 8562090609039612464657923)
      ·
        refine ⟨12843135913559418696986885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8562090609039612464657923 12843135913559418696986885)
        ·
          refine ⟨2408087983792391005685041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12843135913559418696986885 2408087983792391005685041)
          ·
            refine ⟨1806065987844293254263781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2408087983792391005685041 1806065987844293254263781)
            ·
              refine ⟨338637372720804985174459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1806065987844293254263781 338637372720804985174459)
              ·
                refine ⟨507956059081207477761689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 338637372720804985174459 507956059081207477761689)
                ·
                  refine ⟨380967044310905608321267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 507956059081207477761689 380967044310905608321267)
                  ·
                    refine ⟨571450566466358412481901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 380967044310905608321267 571450566466358412481901)
                    ·
                      refine ⟨214293962424884404680713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 571450566466358412481901 214293962424884404680713)
                      ·
                        rfl

theorem cell23_417336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 2, 1, 3].length) (baseStart_417336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417336 prefixEnd_417336 := by exact prefixLift 417336
  have htrace : WordTrace (prefixWord ++ tailWord_417336) baseStart_417336 baseEnd_417336 := by
    simpa [prefixWord, tailWord_417336, baseEnd_417336] using wordTrace_append hprefix tailTrace_417336
  have hstable : (prefixWord ++ tailWord_417336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417336).length < 2 ^ (prefixWord ++ tailWord_417336).sum := by decide
  have hdescent : baseEnd_417336 < baseStart_417336 := by decide
  rcases family_descends (prefixWord ++ tailWord_417336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417355 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 4]
def baseStart_417355 : Nat := 118140960795 + 417355 * 2 ^ 59
def prefixEnd_417355 : Nat := 4983230072969 + 3 ^ 40 * 417355 * 2
def baseEnd_417355 : Nat := 214303718557319830343125

theorem tailTrace_417355 : CollatzResearch.WordTrace tailWord_417355 prefixEnd_417355 214303718557319830343125 := by
  unfold tailWord_417355
  simp only [CollatzResearch.WordTrace]
  refine ⟨15222187403001588404333519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10148124935334392269555679 15222187403001588404333519)
  ·
    refine ⟨22833281104502382606500279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15222187403001588404333519 22833281104502382606500279)
    ·
      refine ⟨34249921656753573909750419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22833281104502382606500279 34249921656753573909750419)
      ·
        refine ⟨51374882485130360864625629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34249921656753573909750419 51374882485130360864625629)
        ·
          refine ⟨19265580931923885324234611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51374882485130360864625629 19265580931923885324234611)
          ·
            refine ⟨28898371397885827986351917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19265580931923885324234611 28898371397885827986351917)
            ·
              refine ⟨10836889274207185494881969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28898371397885827986351917 10836889274207185494881969)
              ·
                refine ⟨8127666955655389121161477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10836889274207185494881969 8127666955655389121161477)
                ·
                  refine ⟨1523937554185385460217777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8127666955655389121161477 1523937554185385460217777)
                  ·
                    refine ⟨1142953165639039095163333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1523937554185385460217777 1142953165639039095163333)
                    ·
                      refine ⟨214303718557319830343125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1142953165639039095163333 214303718557319830343125)
                      ·
                        rfl

theorem cell23_417355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 4].length) (baseStart_417355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417355 prefixEnd_417355 := by exact prefixLift 417355
  have htrace : WordTrace (prefixWord ++ tailWord_417355) baseStart_417355 baseEnd_417355 := by
    simpa [prefixWord, tailWord_417355, baseEnd_417355] using wordTrace_append hprefix tailTrace_417355
  have hstable : (prefixWord ++ tailWord_417355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417355).length < 2 ^ (prefixWord ++ tailWord_417355).sum := by decide
  have hdescent : baseEnd_417355 < baseStart_417355 := by decide
  rcases family_descends (prefixWord ++ tailWord_417355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417362 : List Nat := [3, 2, 2, 1, 2, 2, 2, 1, 2, 1, 5]
def baseStart_417362 : Nat := 118140960795 + 417362 * 2 ^ 59
def prefixEnd_417362 : Nat := 4983230072969 + 3 ^ 40 * 417362 * 2
def baseEnd_417362 : Nat := 214307312921901302955593

theorem tailTrace_417362 : CollatzResearch.WordTrace tailWord_417362 prefixEnd_417362 214307312921901302955593 := by
  unfold tailWord_417362
  simp only [CollatzResearch.WordTrace]
  refine ⟨3805610678494057149959585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10148295142650819066558893 3805610678494057149959585)
  ·
    refine ⟨2854208008870542862469689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3805610678494057149959585 2854208008870542862469689)
    ·
      refine ⟨2140656006652907146852267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2854208008870542862469689 2140656006652907146852267)
      ·
        refine ⟨3210984009979360720278401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2140656006652907146852267 3210984009979360720278401)
        ·
          refine ⟨2408238007484520540208801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3210984009979360720278401 2408238007484520540208801)
          ·
            refine ⟨1806178505613390405156601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2408238007484520540208801 1806178505613390405156601)
            ·
              refine ⟨1354633879210042803867451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1806178505613390405156601 1354633879210042803867451)
              ·
                refine ⟨2031950818815064205801177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1354633879210042803867451 2031950818815064205801177)
                ·
                  refine ⟨1523963114111298154350883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2031950818815064205801177 1523963114111298154350883)
                  ·
                    refine ⟨2285944671166947231526325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1523963114111298154350883 2285944671166947231526325)
                    ·
                      refine ⟨214307312921901302955593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2285944671166947231526325 214307312921901302955593)
                      ·
                        rfl

theorem cell23_417362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_417362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417362 prefixEnd_417362 := by exact prefixLift 417362
  have htrace : WordTrace (prefixWord ++ tailWord_417362) baseStart_417362 baseEnd_417362 := by
    simpa [prefixWord, tailWord_417362, baseEnd_417362] using wordTrace_append hprefix tailTrace_417362
  have hstable : (prefixWord ++ tailWord_417362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417362).length < 2 ^ (prefixWord ++ tailWord_417362).sum := by decide
  have hdescent : baseEnd_417362 < baseStart_417362 := by decide
  rcases family_descends (prefixWord ++ tailWord_417362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417389 : List Nat := [1, 5, 1, 1, 4, 1, 1, 1, 2, 2, 4]
def baseStart_417389 : Nat := 118140960795 + 417389 * 2 ^ 59
def prefixEnd_417389 : Nat := 4983230072969 + 3 ^ 40 * 417389 * 2
def baseEnd_417389 : Nat := 214321176899572697317969

theorem tailTrace_417389 : CollatzResearch.WordTrace tailWord_417389 prefixEnd_417389 214321176899572697317969 := by
  unfold tailWord_417389
  simp only [CollatzResearch.WordTrace]
  refine ⟨15223427484878412211071221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10148951656585608140714147 15223427484878412211071221)
  ·
    refine ⟨1427196326707351144787927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15223427484878412211071221 1427196326707351144787927)
    ·
      refine ⟨2140794490061026717181891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1427196326707351144787927 2140794490061026717181891)
      ·
        refine ⟨3211191735091540075772837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2140794490061026717181891 3211191735091540075772837)
        ·
          refine ⟨602098450329663764207407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3211191735091540075772837 602098450329663764207407)
          ·
            refine ⟨903147675494495646311111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 602098450329663764207407 903147675494495646311111)
            ·
              refine ⟨1354721513241743469466667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 903147675494495646311111 1354721513241743469466667)
              ·
                refine ⟨2032082269862615204200001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1354721513241743469466667 2032082269862615204200001)
                ·
                  refine ⟨1524061702396961403150001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2032082269862615204200001 1524061702396961403150001)
                  ·
                    refine ⟨1143046276797721052362501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1524061702396961403150001 1143046276797721052362501)
                    ·
                      refine ⟨214321176899572697317969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1143046276797721052362501 214321176899572697317969)
                      ·
                        rfl

theorem cell23_417389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_417389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417389 prefixEnd_417389 := by exact prefixLift 417389
  have htrace : WordTrace (prefixWord ++ tailWord_417389) baseStart_417389 baseEnd_417389 := by
    simpa [prefixWord, tailWord_417389, baseEnd_417389] using wordTrace_append hprefix tailTrace_417389
  have hstable : (prefixWord ++ tailWord_417389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417389).length < 2 ^ (prefixWord ++ tailWord_417389).sum := by decide
  have hdescent : baseEnd_417389 < baseStart_417389 := by decide
  rcases family_descends (prefixWord ++ tailWord_417389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417392 : List Nat := [2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 3]
def baseStart_417392 : Nat := 118140960795 + 417392 * 2 ^ 59
def prefixEnd_417392 : Nat := 4983230072969 + 3 ^ 40 * 417392 * 2
def baseEnd_417392 : Nat := 214322717341536185580455

theorem tailTrace_417392 : CollatzResearch.WordTrace tailWord_417392 prefixEnd_417392 214322717341536185580455 := by
  unfold tailWord_417392
  simp only [CollatzResearch.WordTrace]
  refine ⟨7611768451933771861715215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10149024602578362482286953 7611768451933771861715215)
  ·
    refine ⟨11417652677900657792572823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7611768451933771861715215 11417652677900657792572823)
    ·
      refine ⟨17126479016850986688859235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11417652677900657792572823 17126479016850986688859235)
      ·
        refine ⟨25689718525276480033288853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17126479016850986688859235 25689718525276480033288853)
        ·
          refine ⟨1204205555872335001560415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25689718525276480033288853 1204205555872335001560415)
          ·
            refine ⟨1806308333808502502340623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1204205555872335001560415 1806308333808502502340623)
            ·
              refine ⟨2709462500712753753510935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1806308333808502502340623 2709462500712753753510935)
              ·
                refine ⟨4064193751069130630266403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2709462500712753753510935 4064193751069130630266403)
                ·
                  refine ⟨6096290626603695945399605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4064193751069130630266403 6096290626603695945399605)
                  ·
                    refine ⟨571527246244096494881213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6096290626603695945399605 571527246244096494881213)
                    ·
                      refine ⟨214322717341536185580455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 571527246244096494881213 214322717341536185580455)
                      ·
                        rfl

theorem cell23_417392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 3].length) (baseStart_417392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417392 prefixEnd_417392 := by exact prefixLift 417392
  have htrace : WordTrace (prefixWord ++ tailWord_417392) baseStart_417392 baseEnd_417392 := by
    simpa [prefixWord, tailWord_417392, baseEnd_417392] using wordTrace_append hprefix tailTrace_417392
  have hstable : (prefixWord ++ tailWord_417392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417392).length < 2 ^ (prefixWord ++ tailWord_417392).sum := by decide
  have hdescent : baseEnd_417392 < baseStart_417392 := by decide
  rcases family_descends (prefixWord ++ tailWord_417392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417469 : List Nat := [1, 4, 1, 2, 1, 2, 2, 3, 2, 2, 3]
def baseStart_417469 : Nat := 118140960795 + 417469 * 2 ^ 59
def prefixEnd_417469 : Nat := 4983230072969 + 3 ^ 40 * 417469 * 2
def baseEnd_417469 : Nat := 214362255351932384317601

theorem tailTrace_417469 : CollatzResearch.WordTrace tailWord_417469 prefixEnd_417469 214362255351932384317601 := by
  unfold tailWord_417469
  simp only [CollatzResearch.WordTrace]
  refine ⟨15226345324588585873983461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10150896883059057249322307 15226345324588585873983461)
  ·
    refine ⟨2854939748360359851371899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15226345324588585873983461 2854939748360359851371899)
    ·
      refine ⟨4282409622540539777057849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2854939748360359851371899 4282409622540539777057849)
      ·
        refine ⟨3211807216905404832793387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4282409622540539777057849 3211807216905404832793387)
        ·
          refine ⟨4817710825358107249190081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3211807216905404832793387 4817710825358107249190081)
          ·
            refine ⟨3613283119018580436892561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4817710825358107249190081 3613283119018580436892561)
            ·
              refine ⟨2709962339263935327669421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3613283119018580436892561 2709962339263935327669421)
              ·
                refine ⟨1016235877223975747876033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2709962339263935327669421 1016235877223975747876033)
                ·
                  refine ⟨762176907917981810907025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1016235877223975747876033 762176907917981810907025)
                  ·
                    refine ⟨571632680938486358180269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 762176907917981810907025 571632680938486358180269)
                    ·
                      refine ⟨214362255351932384317601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 571632680938486358180269 214362255351932384317601)
                      ·
                        rfl

theorem cell23_417469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_417469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417469 prefixEnd_417469 := by exact prefixLift 417469
  have htrace : WordTrace (prefixWord ++ tailWord_417469) baseStart_417469 baseEnd_417469 := by
    simpa [prefixWord, tailWord_417469, baseEnd_417469] using wordTrace_append hprefix tailTrace_417469
  have hstable : (prefixWord ++ tailWord_417469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417469).length < 2 ^ (prefixWord ++ tailWord_417469).sum := by decide
  have hdescent : baseEnd_417469 < baseStart_417469 := by decide
  rcases family_descends (prefixWord ++ tailWord_417469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417539 : List Nat := [1, 1, 1, 3, 2, 2, 2, 5, 1, 1, 4]
def baseStart_417539 : Nat := 118140960795 + 417539 * 2 ^ 59
def prefixEnd_417539 : Nat := 4983230072969 + 3 ^ 40 * 417539 * 2
def baseEnd_417539 : Nat := 214398198997747110442279

theorem tailTrace_417539 : CollatzResearch.WordTrace tailWord_417539 prefixEnd_417539 214398198997747110442279 := by
  unfold tailWord_417539
  simp only [CollatzResearch.WordTrace]
  refine ⟨15228898434334987829031671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10152598956223325219354447 15228898434334987829031671)
  ·
    refine ⟨22843347651502481743547507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15228898434334987829031671 22843347651502481743547507)
    ·
      refine ⟨34265021477253722615321261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22843347651502481743547507 34265021477253722615321261)
      ·
        refine ⟨12849383053970145980745473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34265021477253722615321261 12849383053970145980745473)
        ·
          refine ⟨9637037290477609485559105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12849383053970145980745473 9637037290477609485559105)
          ·
            refine ⟨7227777967858207114169329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9637037290477609485559105 7227777967858207114169329)
            ·
              refine ⟨5420833475893655335626997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7227777967858207114169329 5420833475893655335626997)
              ·
                refine ⟨508203138365030187715031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5420833475893655335626997 508203138365030187715031)
                ·
                  refine ⟨762304707547545281572547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 508203138365030187715031 762304707547545281572547)
                  ·
                    refine ⟨1143457061321317922358821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 762304707547545281572547 1143457061321317922358821)
                    ·
                      refine ⟨214398198997747110442279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1143457061321317922358821 214398198997747110442279)
                      ·
                        rfl

theorem cell23_417539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 1, 4].length) (baseStart_417539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417539 prefixEnd_417539 := by exact prefixLift 417539
  have htrace : WordTrace (prefixWord ++ tailWord_417539) baseStart_417539 baseEnd_417539 := by
    simpa [prefixWord, tailWord_417539, baseEnd_417539] using wordTrace_append hprefix tailTrace_417539
  have hstable : (prefixWord ++ tailWord_417539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417539).length < 2 ^ (prefixWord ++ tailWord_417539).sum := by decide
  have hdescent : baseEnd_417539 < baseStart_417539 := by decide
  rcases family_descends (prefixWord ++ tailWord_417539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417550 : List Nat := [4, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3]
def baseStart_417550 : Nat := 118140960795 + 417550 * 2 ^ 59
def prefixEnd_417550 : Nat := 4983230072969 + 3 ^ 40 * 417550 * 2
def baseEnd_417550 : Nat := 214403847284946567404729

theorem tailTrace_417550 : CollatzResearch.WordTrace tailWord_417550 prefixEnd_417550 214403847284946567404729 := by
  unfold tailWord_417550
  simp only [CollatzResearch.WordTrace]
  refine ⟨1903662454661892088460263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10152866424863424471788069 1903662454661892088460263)
  ·
    refine ⟨2855493681992838132690395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1903662454661892088460263 2855493681992838132690395)
    ·
      refine ⟨4283240522989257199035593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2855493681992838132690395 4283240522989257199035593)
      ·
        refine ⟨3212430392241942899276695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4283240522989257199035593 3212430392241942899276695)
        ·
          refine ⟨4818645588362914348915043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3212430392241942899276695 4818645588362914348915043)
          ·
            refine ⟨7227968382544371523372565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4818645588362914348915043 7227968382544371523372565)
            ·
              refine ⟨338811017931767415158089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7227968382544371523372565 338811017931767415158089)
              ·
                refine ⟨254108263448825561368567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 338811017931767415158089 254108263448825561368567)
                ·
                  refine ⟨381162395173238342052851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 254108263448825561368567 381162395173238342052851)
                  ·
                    refine ⟨571743592759857513079277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 381162395173238342052851 571743592759857513079277)
                    ·
                      refine ⟨214403847284946567404729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 571743592759857513079277 214403847284946567404729)
                      ·
                        rfl

theorem cell23_417550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3].length) (baseStart_417550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417550 prefixEnd_417550 := by exact prefixLift 417550
  have htrace : WordTrace (prefixWord ++ tailWord_417550) baseStart_417550 baseEnd_417550 := by
    simpa [prefixWord, tailWord_417550, baseEnd_417550] using wordTrace_append hprefix tailTrace_417550
  have hstable : (prefixWord ++ tailWord_417550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417550).length < 2 ^ (prefixWord ++ tailWord_417550).sum := by decide
  have hdescent : baseEnd_417550 < baseStart_417550 := by decide
  rcases family_descends (prefixWord ++ tailWord_417550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417569 : List Nat := [1, 2, 3, 2, 1, 3, 1, 3, 1, 2, 4]
def baseStart_417569 : Nat := 118140960795 + 417569 * 2 ^ 59
def prefixEnd_417569 : Nat := 4983230072969 + 3 ^ 40 * 417569 * 2
def baseEnd_417569 : Nat := 214413603417381993067141

theorem tailTrace_417569 : CollatzResearch.WordTrace tailWord_417569 prefixEnd_417569 214413603417381993067141 := by
  unfold tailWord_417569
  simp only [CollatzResearch.WordTrace]
  refine ⟨15229992624226302952623761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10153328416150868635082507 15229992624226302952623761)
  ·
    refine ⟨11422494468169727214467821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15229992624226302952623761 11422494468169727214467821)
    ·
      refine ⟨4283435425563647705425433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11422494468169727214467821 4283435425563647705425433)
      ·
        refine ⟨3212576569172735779069075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4283435425563647705425433 3212576569172735779069075)
        ·
          refine ⟨4818864853759103668603613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3212576569172735779069075 4818864853759103668603613)
          ·
            refine ⟨1807074320159663875726355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4818864853759103668603613 1807074320159663875726355)
            ·
              refine ⟨2710611480239495813589533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1807074320159663875726355 2710611480239495813589533)
              ·
                refine ⟨1016479305089810930096075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2710611480239495813589533 1016479305089810930096075)
                ·
                  refine ⟨1524718957634716395144113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1016479305089810930096075 1524718957634716395144113)
                  ·
                    refine ⟨1143539218226037296358085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1524718957634716395144113 1143539218226037296358085)
                    ·
                      refine ⟨214413603417381993067141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1143539218226037296358085 214413603417381993067141)
                      ·
                        rfl

theorem cell23_417569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_417569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417569 prefixEnd_417569 := by exact prefixLift 417569
  have htrace : WordTrace (prefixWord ++ tailWord_417569) baseStart_417569 baseEnd_417569 := by
    simpa [prefixWord, tailWord_417569, baseEnd_417569] using wordTrace_append hprefix tailTrace_417569
  have hstable : (prefixWord ++ tailWord_417569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417569).length < 2 ^ (prefixWord ++ tailWord_417569).sum := by decide
  have hdescent : baseEnd_417569 < baseStart_417569 := by decide
  rcases family_descends (prefixWord ++ tailWord_417569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417573 : List Nat := [1, 3, 1, 2, 3, 3, 1, 2, 3, 2, 2]
def baseStart_417573 : Nat := 118140960795 + 417573 * 2 ^ 59
def prefixEnd_417573 : Nat := 4983230072969 + 3 ^ 40 * 417573 * 2
def baseEnd_417573 : Nat := 214415657339999977417123

theorem tailTrace_417573 : CollatzResearch.WordTrace tailWord_417573 prefixEnd_417573 214415657339999977417123 := by
  unfold tailWord_417573
  simp only [CollatzResearch.WordTrace]
  refine ⟨15230138516211811635769373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10153425677474541090512915 15230138516211811635769373)
  ·
    refine ⟨5711301943579429363413515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15230138516211811635769373 5711301943579429363413515)
    ·
      refine ⟨8566952915369144045120273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5711301943579429363413515 8566952915369144045120273)
      ·
        refine ⟨6425214686526858033840205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8566952915369144045120273 6425214686526858033840205)
        ·
          refine ⟨2409455507447571762690077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6425214686526858033840205 2409455507447571762690077)
          ·
            refine ⟨903545815292839411008779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2409455507447571762690077 903545815292839411008779)
            ·
              refine ⟨1355318722939259116513169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 903545815292839411008779 1355318722939259116513169)
              ·
                refine ⟨1016489042204444337384877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1355318722939259116513169 1016489042204444337384877)
                ·
                  refine ⟨381183390826666626519329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1016489042204444337384877 381183390826666626519329)
                  ·
                    refine ⟨285887543119999969889497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 381183390826666626519329 285887543119999969889497)
                    ·
                      refine ⟨214415657339999977417123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 285887543119999969889497 214415657339999977417123)
                      ·
                        rfl

theorem cell23_417573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 3, 2, 2].length) (baseStart_417573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417573 prefixEnd_417573 := by exact prefixLift 417573
  have htrace : WordTrace (prefixWord ++ tailWord_417573) baseStart_417573 baseEnd_417573 := by
    simpa [prefixWord, tailWord_417573, baseEnd_417573] using wordTrace_append hprefix tailTrace_417573
  have hstable : (prefixWord ++ tailWord_417573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417573).length < 2 ^ (prefixWord ++ tailWord_417573).sum := by decide
  have hdescent : baseEnd_417573 < baseStart_417573 := by decide
  rcases family_descends (prefixWord ++ tailWord_417573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417576 : List Nat := [2, 1, 5, 1, 1, 2, 2, 1, 3, 2, 3]
def baseStart_417576 : Nat := 118140960795 + 417576 * 2 ^ 59
def prefixEnd_417576 : Nat := 4983230072969 + 3 ^ 40 * 417576 * 2
def baseEnd_417576 : Nat := 214417197781963465679609

theorem tailTrace_417576 : CollatzResearch.WordTrace tailWord_417576 prefixEnd_417576 214417197781963465679609 := by
  unfold tailWord_417576
  simp only [CollatzResearch.WordTrace]
  refine ⟨7615123967600471574064291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10153498623467295432085721 7615123967600471574064291)
  ·
    refine ⟨11422685951400707361096437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7615123967600471574064291 11422685951400707361096437)
    ·
      refine ⟨1070876807943816315102791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11422685951400707361096437 1070876807943816315102791)
      ·
        refine ⟨1606315211915724472654187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1070876807943816315102791 1606315211915724472654187)
        ·
          refine ⟨2409472817873586708981281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1606315211915724472654187 2409472817873586708981281)
          ·
            refine ⟨1807104613405190031735961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2409472817873586708981281 1807104613405190031735961)
            ·
              refine ⟨1355328460053892523801971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1807104613405190031735961 1355328460053892523801971)
              ·
                refine ⟨2032992690080838785702957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1355328460053892523801971 2032992690080838785702957)
                ·
                  refine ⟨762372258780314544638609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2032992690080838785702957 762372258780314544638609)
                  ·
                    refine ⟨571779194085235908478957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 762372258780314544638609 571779194085235908478957)
                    ·
                      refine ⟨214417197781963465679609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 571779194085235908478957 214417197781963465679609)
                      ·
                        rfl

theorem cell23_417576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_417576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417576 prefixEnd_417576 := by exact prefixLift 417576
  have htrace : WordTrace (prefixWord ++ tailWord_417576) baseStart_417576 baseEnd_417576 := by
    simpa [prefixWord, tailWord_417576, baseEnd_417576] using wordTrace_append hprefix tailTrace_417576
  have hstable : (prefixWord ++ tailWord_417576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417576).length < 2 ^ (prefixWord ++ tailWord_417576).sum := by decide
  have hdescent : baseEnd_417576 < baseStart_417576 := by decide
  rcases family_descends (prefixWord ++ tailWord_417576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417590 : List Nat := [5, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4]
def baseStart_417590 : Nat := 118140960795 + 417590 * 2 ^ 59
def prefixEnd_417590 : Nat := 4983230072969 + 3 ^ 40 * 417590 * 2
def baseEnd_417590 : Nat := 214424386511126410904545

theorem tailTrace_417590 : CollatzResearch.WordTrace tailWord_417590 prefixEnd_417590 214424386511126410904545 := by
  unfold tailWord_417590
  simp only [CollatzResearch.WordTrace]
  refine ⟨951922409821888971196139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10153839038100149026092149 951922409821888971196139)
  ·
    refine ⟨1427883614732833456794209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 951922409821888971196139 1427883614732833456794209)
    ·
      refine ⟨1070912711049625092595657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1427883614732833456794209 1070912711049625092595657)
      ·
        refine ⟨803184533287218819446743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1070912711049625092595657 803184533287218819446743)
        ·
          refine ⟨1204776799930828229170115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 803184533287218819446743 1204776799930828229170115)
          ·
            refine ⟨1807165199896242343755173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1204776799930828229170115 1807165199896242343755173)
            ·
              refine ⟨338843474980545439454095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1807165199896242343755173 338843474980545439454095)
              ·
                refine ⟨508265212470818159181143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 338843474980545439454095 508265212470818159181143)
                ·
                  refine ⟨762397818706227238771715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 508265212470818159181143 762397818706227238771715)
                  ·
                    refine ⟨1143596728059340858157573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 762397818706227238771715 1143596728059340858157573)
                    ·
                      refine ⟨214424386511126410904545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1143596728059340858157573 214424386511126410904545)
                      ·
                        rfl

theorem cell23_417590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_417590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417590 prefixEnd_417590 := by exact prefixLift 417590
  have htrace : WordTrace (prefixWord ++ tailWord_417590) baseStart_417590 baseEnd_417590 := by
    simpa [prefixWord, tailWord_417590, baseEnd_417590] using wordTrace_append hprefix tailTrace_417590
  have hstable : (prefixWord ++ tailWord_417590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417590).length < 2 ^ (prefixWord ++ tailWord_417590).sum := by decide
  have hdescent : baseEnd_417590 < baseStart_417590 := by decide
  rcases family_descends (prefixWord ++ tailWord_417590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417623 : List Nat := [1, 1, 3, 2, 5, 2, 1, 1, 1, 3, 3]
def baseStart_417623 : Nat := 118140960795 + 417623 * 2 ^ 59
def prefixEnd_417623 : Nat := 4983230072969 + 3 ^ 40 * 417623 * 2
def baseEnd_417623 : Nat := 214441331372724781791893

theorem tailTrace_417623 : CollatzResearch.WordTrace tailWord_417623 prefixEnd_417623 214441331372724781791893 := by
  unfold tailWord_417623
  simp only [CollatzResearch.WordTrace]
  refine ⟨15231962166030670175089523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10154641444020446783393015 15231962166030670175089523)
  ·
    refine ⟨22847943249046005262634285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15231962166030670175089523 22847943249046005262634285)
    ·
      refine ⟨8567978718392251973487857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22847943249046005262634285 8567978718392251973487857)
      ·
        refine ⟨6425984038794188980115893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8567978718392251973487857 6425984038794188980115893)
        ·
          refine ⟨602436003636955216885865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6425984038794188980115893 602436003636955216885865)
          ·
            refine ⟨451827002727716412664399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 602436003636955216885865 451827002727716412664399)
            ·
              refine ⟨677740504091574618996599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 451827002727716412664399 677740504091574618996599)
              ·
                refine ⟨1016610756137361928494899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 677740504091574618996599 1016610756137361928494899)
                ·
                  refine ⟨1524916134206042892742349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1016610756137361928494899 1524916134206042892742349)
                  ·
                    refine ⟨571843550327266084778381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1524916134206042892742349 571843550327266084778381)
                    ·
                      refine ⟨214441331372724781791893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 571843550327266084778381 214441331372724781791893)
                      ·
                        rfl

theorem cell23_417623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 3, 3].length) (baseStart_417623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417623 prefixEnd_417623 := by exact prefixLift 417623
  have htrace : WordTrace (prefixWord ++ tailWord_417623) baseStart_417623 baseEnd_417623 := by
    simpa [prefixWord, tailWord_417623, baseEnd_417623] using wordTrace_append hprefix tailTrace_417623
  have hstable : (prefixWord ++ tailWord_417623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417623).length < 2 ^ (prefixWord ++ tailWord_417623).sum := by decide
  have hdescent : baseEnd_417623 < baseStart_417623 := by decide
  rcases family_descends (prefixWord ++ tailWord_417623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417633 : List Nat := [1, 2, 3, 1, 1, 1, 6, 2, 1, 3, 2]
def baseStart_417633 : Nat := 118140960795 + 417633 * 2 ^ 59
def prefixEnd_417633 : Nat := 4983230072969 + 3 ^ 40 * 417633 * 2
def baseEnd_417633 : Nat := 214446466179269742666847

theorem tailTrace_417633 : CollatzResearch.WordTrace tailWord_417633 prefixEnd_417633 214446466179269742666847 := by
  unfold tailWord_417633
  simp only [CollatzResearch.WordTrace]
  refine ⟨15232326895994441882953553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10154884597329627921969035 15232326895994441882953553)
  ·
    refine ⟨11424245171995831412215165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15232326895994441882953553 11424245171995831412215165)
    ·
      refine ⟨4284091939498436779580687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11424245171995831412215165 4284091939498436779580687)
      ·
        refine ⟨6426137909247655169371031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4284091939498436779580687 6426137909247655169371031)
        ·
          refine ⟨9639206863871482754056547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6426137909247655169371031 9639206863871482754056547)
          ·
            refine ⟨14458810295807224131084821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9639206863871482754056547 14458810295807224131084821)
            ·
              refine ⟨677756732615963631144601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14458810295807224131084821 677756732615963631144601)
              ·
                refine ⟨508317549461972723358451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 677756732615963631144601 508317549461972723358451)
                ·
                  refine ⟨762476324192959085037677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 508317549461972723358451 762476324192959085037677)
                  ·
                    refine ⟨285928621572359656889129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 762476324192959085037677 285928621572359656889129)
                    ·
                      refine ⟨214446466179269742666847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 285928621572359656889129 214446466179269742666847)
                      ·
                        rfl

theorem cell23_417633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 3, 2].length) (baseStart_417633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417633 prefixEnd_417633 := by exact prefixLift 417633
  have htrace : WordTrace (prefixWord ++ tailWord_417633) baseStart_417633 baseEnd_417633 := by
    simpa [prefixWord, tailWord_417633, baseEnd_417633] using wordTrace_append hprefix tailTrace_417633
  have hstable : (prefixWord ++ tailWord_417633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417633).length < 2 ^ (prefixWord ++ tailWord_417633).sum := by decide
  have hdescent : baseEnd_417633 < baseStart_417633 := by decide
  rcases family_descends (prefixWord ++ tailWord_417633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417649 : List Nat := [1, 2, 2, 2, 1, 3, 3, 1, 2, 1, 5]
def baseStart_417649 : Nat := 118140960795 + 417649 * 2 ^ 59
def prefixEnd_417649 : Nat := 4983230072969 + 3 ^ 40 * 417649 * 2
def baseEnd_417649 : Nat := 214454681869741680066773

theorem tailTrace_417649 : CollatzResearch.WordTrace tailWord_417649 prefixEnd_417649 214454681869741680066773 := by
  unfold tailWord_417649
  simp only [CollatzResearch.WordTrace]
  refine ⟨15232910463936476615536001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10155273642624317743690667 15232910463936476615536001)
  ·
    refine ⟨11424682847952357461652001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15232910463936476615536001 11424682847952357461652001)
    ·
      refine ⟨8568512135964268096239001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11424682847952357461652001 8568512135964268096239001)
      ·
        refine ⟨6426384101973201072179251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8568512135964268096239001 6426384101973201072179251)
        ·
          refine ⟨9639576152959801608268877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6426384101973201072179251 9639576152959801608268877)
          ·
            refine ⟨3614841057359925603100829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9639576152959801608268877 3614841057359925603100829)
            ·
              refine ⟨1355565396509972101162811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3614841057359925603100829 1355565396509972101162811)
              ·
                refine ⟨2033348094764958151744217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1355565396509972101162811 2033348094764958151744217)
                ·
                  refine ⟨1525011071073718613808163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2033348094764958151744217 1525011071073718613808163)
                  ·
                    refine ⟨2287516606610577920712245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1525011071073718613808163 2287516606610577920712245)
                    ·
                      refine ⟨214454681869741680066773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2287516606610577920712245 214454681869741680066773)
                      ·
                        rfl

theorem cell23_417649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_417649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417649 prefixEnd_417649 := by exact prefixLift 417649
  have htrace : WordTrace (prefixWord ++ tailWord_417649) baseStart_417649 baseEnd_417649 := by
    simpa [prefixWord, tailWord_417649, baseEnd_417649] using wordTrace_append hprefix tailTrace_417649
  have hstable : (prefixWord ++ tailWord_417649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417649).length < 2 ^ (prefixWord ++ tailWord_417649).sum := by decide
  have hdescent : baseEnd_417649 < baseStart_417649 := by decide
  rcases family_descends (prefixWord ++ tailWord_417649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417663 : List Nat := [1, 1, 2, 2, 1, 1, 3, 6, 2, 2, 2]
def baseStart_417663 : Nat := 118140960795 + 417663 * 2 ^ 59
def prefixEnd_417663 : Nat := 4983230072969 + 3 ^ 40 * 417663 * 2
def baseEnd_417663 : Nat := 214461870598904625291709

theorem tailTrace_417663 : CollatzResearch.WordTrace tailWord_417663 prefixEnd_417663 214461870598904625291709 := by
  unfold tailWord_417663
  simp only [CollatzResearch.WordTrace]
  refine ⟨15233421085885757006545643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10155614057257171337697095 15233421085885757006545643)
  ·
    refine ⟨22850131628828635509818465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15233421085885757006545643 22850131628828635509818465)
    ·
      refine ⟨17137598721621476632363849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22850131628828635509818465 17137598721621476632363849)
      ·
        refine ⟨12853199041216107474272887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17137598721621476632363849 12853199041216107474272887)
        ·
          refine ⟨19279798561824161211409331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12853199041216107474272887 19279798561824161211409331)
          ·
            refine ⟨28919697842736241817113997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19279798561824161211409331 28919697842736241817113997)
            ·
              refine ⟨10844886691026090681417749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28919697842736241817113997 10844886691026090681417749)
              ·
                refine ⟨508354063641848000691457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10844886691026090681417749 508354063641848000691457)
                ·
                  refine ⟨381265547731386000518593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 508354063641848000691457 381265547731386000518593)
                  ·
                    refine ⟨285949160798539500388945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 381265547731386000518593 285949160798539500388945)
                    ·
                      refine ⟨214461870598904625291709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 285949160798539500388945 214461870598904625291709)
                      ·
                        rfl

theorem cell23_417663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 2, 2, 2].length) (baseStart_417663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417663 prefixEnd_417663 := by exact prefixLift 417663
  have htrace : WordTrace (prefixWord ++ tailWord_417663) baseStart_417663 baseEnd_417663 := by
    simpa [prefixWord, tailWord_417663, baseEnd_417663] using wordTrace_append hprefix tailTrace_417663
  have hstable : (prefixWord ++ tailWord_417663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417663).length < 2 ^ (prefixWord ++ tailWord_417663).sum := by decide
  have hdescent : baseEnd_417663 < baseStart_417663 := by decide
  rcases family_descends (prefixWord ++ tailWord_417663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417674 : List Nat := [3, 1, 2, 4, 3, 1, 2, 1, 2, 1, 3]
def baseStart_417674 : Nat := 118140960795 + 417674 * 2 ^ 59
def prefixEnd_417674 : Nat := 4983230072969 + 3 ^ 40 * 417674 * 2
def baseEnd_417674 : Nat := 214467518886104082254159

theorem tailTrace_417674 : CollatzResearch.WordTrace tailWord_417674 prefixEnd_417674 214467518886104082254159 := by
  unfold tailWord_417674
  simp only [CollatzResearch.WordTrace]
  refine ⟨3808455572211476471299019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10155881525897270590130717 3808455572211476471299019)
  ·
    refine ⟨5712683358317214706948529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3808455572211476471299019 5712683358317214706948529)
    ·
      refine ⟨4284512518737911030211397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5712683358317214706948529 4284512518737911030211397)
      ·
        refine ⟨803346097263358318164637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4284512518737911030211397 803346097263358318164637)
        ·
          refine ⟨301254786473759369311739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 803346097263358318164637 301254786473759369311739)
          ·
            refine ⟨451882179710639053967609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301254786473759369311739 451882179710639053967609)
            ·
              refine ⟨338911634782979290475707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 451882179710639053967609 338911634782979290475707)
              ·
                refine ⟨508367452174468935713561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 338911634782979290475707 508367452174468935713561)
                ·
                  refine ⟨381275589130851701785171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 508367452174468935713561 381275589130851701785171)
                  ·
                    refine ⟨571913383696277552677757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 381275589130851701785171 571913383696277552677757)
                    ·
                      refine ⟨214467518886104082254159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 571913383696277552677757 214467518886104082254159)
                      ·
                        rfl

theorem cell23_417674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_417674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417674 prefixEnd_417674 := by exact prefixLift 417674
  have htrace : WordTrace (prefixWord ++ tailWord_417674) baseStart_417674 baseEnd_417674 := by
    simpa [prefixWord, tailWord_417674, baseEnd_417674] using wordTrace_append hprefix tailTrace_417674
  have hstable : (prefixWord ++ tailWord_417674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417674).length < 2 ^ (prefixWord ++ tailWord_417674).sum := by decide
  have hdescent : baseEnd_417674 < baseStart_417674 := by decide
  rcases family_descends (prefixWord ++ tailWord_417674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417679 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 8, 3, 3]
def baseStart_417679 : Nat := 118140960795 + 417679 * 2 ^ 59
def prefixEnd_417679 : Nat := 4983230072969 + 3 ^ 40 * 417679 * 2
def baseEnd_417679 : Nat := 214470086289376562691635

theorem tailTrace_417679 : CollatzResearch.WordTrace tailWord_417679 prefixEnd_417679 214470086289376562691635 := by
  unfold tailWord_417679
  simp only [CollatzResearch.WordTrace]
  refine ⟨15234004653827791739128091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10156003102551861159418727 15234004653827791739128091)
  ·
    refine ⟨22851006980741687608692137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15234004653827791739128091 22851006980741687608692137)
    ·
      refine ⟨17138255235556265706519103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22851006980741687608692137 17138255235556265706519103)
      ·
        refine ⟨25707382853334398559778655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17138255235556265706519103 25707382853334398559778655)
        ·
          refine ⟨38561074280001597839667983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25707382853334398559778655 38561074280001597839667983)
          ·
            refine ⟨57841611420002396759501975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38561074280001597839667983 57841611420002396759501975)
            ·
              refine ⟨86762417130003595139252963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57841611420002396759501975 86762417130003595139252963)
              ·
                refine ⟨130143625695005392708879445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86762417130003595139252963 130143625695005392708879445)
                ·
                  refine ⟨1525120613613344445807181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 130143625695005392708879445 1525120613613344445807181)
                  ·
                    refine ⟨571920230105004167177693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1525120613613344445807181 571920230105004167177693)
                    ·
                      refine ⟨214470086289376562691635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 571920230105004167177693 214470086289376562691635)
                      ·
                        rfl

theorem cell23_417679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 3, 3].length) (baseStart_417679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417679 prefixEnd_417679 := by exact prefixLift 417679
  have htrace : WordTrace (prefixWord ++ tailWord_417679) baseStart_417679 baseEnd_417679 := by
    simpa [prefixWord, tailWord_417679, baseEnd_417679] using wordTrace_append hprefix tailTrace_417679
  have hstable : (prefixWord ++ tailWord_417679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417679).length < 2 ^ (prefixWord ++ tailWord_417679).sum := by decide
  have hdescent : baseEnd_417679 < baseStart_417679 := by decide
  rcases family_descends (prefixWord ++ tailWord_417679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417719 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 4]
def baseStart_417719 : Nat := 118140960795 + 417719 * 2 ^ 59
def prefixEnd_417719 : Nat := 4983230072969 + 3 ^ 40 * 417719 * 2
def baseEnd_417719 : Nat := 214490625515556406191451

theorem tailTrace_417719 : CollatzResearch.WordTrace tailWord_417719 prefixEnd_417719 214490625515556406191451 := by
  unfold tailWord_417719
  simp only [CollatzResearch.WordTrace]
  refine ⟨15235463573682878570584211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10156975715788585713722807 15235463573682878570584211)
  ·
    refine ⟨22853195360524317855876317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15235463573682878570584211 22853195360524317855876317)
    ·
      refine ⟨8569948260196619195953619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22853195360524317855876317 8569948260196619195953619)
      ·
        refine ⟨12854922390294928793930429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8569948260196619195953619 12854922390294928793930429)
        ·
          refine ⟨4820595896360598297723911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12854922390294928793930429 4820595896360598297723911)
          ·
            refine ⟨7230893844540897446585867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4820595896360598297723911 7230893844540897446585867)
            ·
              refine ⟨10846340766811346169878801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7230893844540897446585867 10846340766811346169878801)
              ·
                refine ⟨8134755575108509627409101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10846340766811346169878801 8134755575108509627409101)
                ·
                  refine ⟨3050533340665691110278413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8134755575108509627409101 3050533340665691110278413)
                  ·
                    refine ⟨1143950002749634166354405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3050533340665691110278413 1143950002749634166354405)
                    ·
                      refine ⟨214490625515556406191451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1143950002749634166354405 214490625515556406191451)
                      ·
                        rfl

theorem cell23_417719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 4].length) (baseStart_417719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417719 prefixEnd_417719 := by exact prefixLift 417719
  have htrace : WordTrace (prefixWord ++ tailWord_417719) baseStart_417719 baseEnd_417719 := by
    simpa [prefixWord, tailWord_417719, baseEnd_417719] using wordTrace_append hprefix tailTrace_417719
  have hstable : (prefixWord ++ tailWord_417719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417719).length < 2 ^ (prefixWord ++ tailWord_417719).sum := by decide
  have hdescent : baseEnd_417719 < baseStart_417719 := by decide
  rcases family_descends (prefixWord ++ tailWord_417719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417726 : List Nat := [4, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5]
def baseStart_417726 : Nat := 118140960795 + 417726 * 2 ^ 59
def prefixEnd_417726 : Nat := 4983230072969 + 3 ^ 40 * 417726 * 2
def baseEnd_417726 : Nat := 214494219880137878803919

theorem tailTrace_417726 : CollatzResearch.WordTrace tailWord_417726 prefixEnd_417726 214494219880137878803919 := by
  unfold tailWord_417726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1904464860582189845761129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10157145923105012510726021 1904464860582189845761129)
  ·
    refine ⟨1428348645436642384320847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1904464860582189845761129 1428348645436642384320847)
    ·
      refine ⟨2142522968154963576481271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1428348645436642384320847 2142522968154963576481271)
      ·
        refine ⟨3213784452232445364721907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2142522968154963576481271 3213784452232445364721907)
        ·
          refine ⟨4820676678348668047082861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3213784452232445364721907 4820676678348668047082861)
          ·
            refine ⟨1807753754380750517656073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4820676678348668047082861 1807753754380750517656073)
            ·
              refine ⟨1355815315785562888242055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1807753754380750517656073 1355815315785562888242055)
              ·
                refine ⟨2033722973678344332363083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1355815315785562888242055 2033722973678344332363083)
                ·
                  refine ⟨3050584460517516498544625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2033722973678344332363083 3050584460517516498544625)
                  ·
                    refine ⟨2287938345388137373908469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3050584460517516498544625 2287938345388137373908469)
                    ·
                      refine ⟨214494219880137878803919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2287938345388137373908469 214494219880137878803919)
                      ·
                        rfl

theorem cell23_417726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_417726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417726 prefixEnd_417726 := by exact prefixLift 417726
  have htrace : WordTrace (prefixWord ++ tailWord_417726) baseStart_417726 baseEnd_417726 := by
    simpa [prefixWord, tailWord_417726, baseEnd_417726] using wordTrace_append hprefix tailTrace_417726
  have hstable : (prefixWord ++ tailWord_417726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417726).length < 2 ^ (prefixWord ++ tailWord_417726).sum := by decide
  have hdescent : baseEnd_417726 < baseStart_417726 := by decide
  rcases family_descends (prefixWord ++ tailWord_417726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417776 : List Nat := [2, 1, 1, 1, 3, 2, 5, 2, 6]
def baseStart_417776 : Nat := 118140960795 + 417776 * 2 ^ 59
def prefixEnd_417776 : Nat := 4983230072969 + 3 ^ 40 * 417776 * 2
def baseEnd_417776 : Nat := 23835543768095853686521

theorem tailTrace_417776 : CollatzResearch.WordTrace tailWord_417776 prefixEnd_417776 23835543768095853686521 := by
  unfold tailWord_417776
  simp only [CollatzResearch.WordTrace]
  refine ⟨7618771267238188652704591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10158361689650918203606121 7618771267238188652704591)
  ·
    refine ⟨11428156900857282979056887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7618771267238188652704591 11428156900857282979056887)
    ·
      refine ⟨17142235351285924468585331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11428156900857282979056887 17142235351285924468585331)
      ·
        refine ⟨25713353026928886702877997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17142235351285924468585331 25713353026928886702877997)
        ·
          refine ⟨9642507385098332513579249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25713353026928886702877997 9642507385098332513579249)
          ·
            refine ⟨7231880538823749385184437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9642507385098332513579249 7231880538823749385184437)
            ·
              refine ⟨677988800514726504861041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7231880538823749385184437 677988800514726504861041)
              ·
                refine ⟨508491600386044878645781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 677988800514726504861041 508491600386044878645781)
                ·
                  refine ⟨23835543768095853686521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 508491600386044878645781 23835543768095853686521)
                  ·
                    rfl

theorem cell23_417776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 6].length) (baseStart_417776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417776 prefixEnd_417776 := by exact prefixLift 417776
  have htrace : WordTrace (prefixWord ++ tailWord_417776) baseStart_417776 baseEnd_417776 := by
    simpa [prefixWord, tailWord_417776, baseEnd_417776] using wordTrace_append hprefix tailTrace_417776
  have hstable : (prefixWord ++ tailWord_417776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417776).length < 2 ^ (prefixWord ++ tailWord_417776).sum := by decide
  have hdescent : baseEnd_417776 < baseStart_417776 := by decide
  rcases family_descends (prefixWord ++ tailWord_417776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417793 : List Nat := [1, 2, 4, 1, 2, 1, 5, 1, 6]
def baseStart_417793 : Nat := 118140960795 + 417793 * 2 ^ 59
def prefixEnd_417793 : Nat := 4983230072969 + 3 ^ 40 * 417793 * 2
def baseEnd_417793 : Nat := 23836513675998790740679

theorem tailTrace_417793 : CollatzResearch.WordTrace tailWord_417793 prefixEnd_417793 23836513675998790740679 := by
  unfold tailWord_417793
  simp only [CollatzResearch.WordTrace]
  refine ⟨15238162575414789208778033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10158775050276526139185355 15238162575414789208778033)
  ·
    refine ⟨11428621931561091906583525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15238162575414789208778033 11428621931561091906583525)
    ·
      refine ⟨2142866612167704732484411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11428621931561091906583525 2142866612167704732484411)
      ·
        refine ⟨3214299918251557098726617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2142866612167704732484411 3214299918251557098726617)
        ·
          refine ⟨2410724938688667824044963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3214299918251557098726617 2410724938688667824044963)
          ·
            refine ⟨3616087408033001736067445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2410724938688667824044963 3616087408033001736067445)
            ·
              refine ⟨339008194503093912756323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3616087408033001736067445 339008194503093912756323)
              ·
                refine ⟨508512291754640869134485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 339008194503093912756323 508512291754640869134485)
                ·
                  refine ⟨23836513675998790740679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 508512291754640869134485 23836513675998790740679)
                  ·
                    rfl

theorem cell23_417793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 6].length) (baseStart_417793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417793 prefixEnd_417793 := by exact prefixLift 417793
  have htrace : WordTrace (prefixWord ++ tailWord_417793) baseStart_417793 baseEnd_417793 := by
    simpa [prefixWord, tailWord_417793, baseEnd_417793] using wordTrace_append hprefix tailTrace_417793
  have hstable : (prefixWord ++ tailWord_417793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417793).length < 2 ^ (prefixWord ++ tailWord_417793).sum := by decide
  have hdescent : baseEnd_417793 < baseStart_417793 := by decide
  rcases family_descends (prefixWord ++ tailWord_417793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417803 : List Nat := [1, 1, 1, 1, 6, 1, 1, 4, 3, 1, 3]
def baseStart_417803 : Nat := 118140960795 + 417803 * 2 ^ 59
def prefixEnd_417803 : Nat := 4983230072969 + 3 ^ 40 * 417803 * 2
def baseEnd_417803 : Nat := 214533757890534077541065

theorem tailTrace_417803 : CollatzResearch.WordTrace tailWord_417803 prefixEnd_417803 214533757890534077541065 := by
  unfold tailWord_417803
  simp only [CollatzResearch.WordTrace]
  refine ⟨15238527305378560916642063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10159018203585707277761375 15238527305378560916642063)
  ·
    refine ⟨22857790958067841374963095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15238527305378560916642063 22857790958067841374963095)
    ·
      refine ⟨34286686437101762062444643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22857790958067841374963095 34286686437101762062444643)
      ·
        refine ⟨51430029655652643093666965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34286686437101762062444643 51430029655652643093666965)
        ·
          refine ⟨2410782640108717645015639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 51430029655652643093666965 2410782640108717645015639)
          ·
            refine ⟨3616173960163076467523459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2410782640108717645015639 3616173960163076467523459)
            ·
              refine ⟨5424260940244614701285189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3616173960163076467523459 5424260940244614701285189)
              ·
                refine ⟨1017048926295865256490973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5424260940244614701285189 1017048926295865256490973)
                ·
                  refine ⟨381393347360949471184115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1017048926295865256490973 381393347360949471184115)
                  ·
                    refine ⟨572090021041424206776173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 381393347360949471184115 572090021041424206776173)
                    ·
                      refine ⟨214533757890534077541065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 572090021041424206776173 214533757890534077541065)
                      ·
                        rfl

theorem cell23_417803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 3, 1, 3].length) (baseStart_417803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417803 prefixEnd_417803 := by exact prefixLift 417803
  have htrace : WordTrace (prefixWord ++ tailWord_417803) baseStart_417803 baseEnd_417803 := by
    simpa [prefixWord, tailWord_417803, baseEnd_417803] using wordTrace_append hprefix tailTrace_417803
  have hstable : (prefixWord ++ tailWord_417803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417803).length < 2 ^ (prefixWord ++ tailWord_417803).sum := by decide
  have hdescent : baseEnd_417803 < baseStart_417803 := by decide
  rcases family_descends (prefixWord ++ tailWord_417803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417844 : List Nat := [2, 5, 1, 2, 3, 1, 2, 1, 6]
def baseStart_417844 : Nat := 118140960795 + 417844 * 2 ^ 59
def prefixEnd_417844 : Nat := 4983230072969 + 3 ^ 40 * 417844 * 2
def baseEnd_417844 : Nat := 23839423399707601903153

theorem tailTrace_417844 : CollatzResearch.WordTrace tailWord_417844 prefixEnd_417844 23839423399707601903153 := by
  unfold tailWord_417844
  simp only [CollatzResearch.WordTrace]
  refine ⟨7620011349115012459442293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10160015132153349945923057 7620011349115012459442293)
  ·
    refine ⟨714376063979532418072715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7620011349115012459442293 714376063979532418072715)
    ·
      refine ⟨1071564095969298627109073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 714376063979532418072715 1071564095969298627109073)
      ·
        refine ⟨803673071976973970331805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1071564095969298627109073 803673071976973970331805)
        ·
          refine ⟨301377401991365238874427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 803673071976973970331805 301377401991365238874427)
          ·
            refine ⟨452066102987047858311641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301377401991365238874427 452066102987047858311641)
            ·
              refine ⟨339049577240285893733731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 452066102987047858311641 339049577240285893733731)
              ·
                refine ⟨508574365860428840600597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 339049577240285893733731 508574365860428840600597)
                ·
                  refine ⟨23839423399707601903153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 508574365860428840600597 23839423399707601903153)
                  ·
                    rfl

theorem cell23_417844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_417844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417844 prefixEnd_417844 := by exact prefixLift 417844
  have htrace : WordTrace (prefixWord ++ tailWord_417844) baseStart_417844 baseEnd_417844 := by
    simpa [prefixWord, tailWord_417844, baseEnd_417844] using wordTrace_append hprefix tailTrace_417844
  have hstable : (prefixWord ++ tailWord_417844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417844).length < 2 ^ (prefixWord ++ tailWord_417844).sum := by decide
  have hdescent : baseEnd_417844 < baseStart_417844 := by decide
  rcases family_descends (prefixWord ++ tailWord_417844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417856 : List Nat := [2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 6]
def baseStart_417856 : Nat := 118140960795 + 417856 * 2 ^ 59
def prefixEnd_417856 : Nat := 4983230072969 + 3 ^ 40 * 417856 * 2
def baseEnd_417856 : Nat := 214560972365222370178321

theorem tailTrace_417856 : CollatzResearch.WordTrace tailWord_417856 prefixEnd_417856 214560972365222370178321 := by
  unfold tailWord_417856
  simp only [CollatzResearch.WordTrace]
  refine ⟨7620230187093275484160711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10160306916124367312214281 7620230187093275484160711)
  ·
    refine ⟨11430345280639913226241067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7620230187093275484160711 11430345280639913226241067)
    ·
      refine ⟨17145517920959869839361601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11430345280639913226241067 17145517920959869839361601)
      ·
        refine ⟨12859138440719902379521201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17145517920959869839361601 12859138440719902379521201)
        ·
          refine ⟨9644353830539926784640901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12859138440719902379521201 9644353830539926784640901)
          ·
            refine ⟨1808316343226236272120169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9644353830539926784640901 1808316343226236272120169)
            ·
              refine ⟨1356237257419677204090127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1808316343226236272120169 1356237257419677204090127)
              ·
                refine ⟨2034355886129515806135191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1356237257419677204090127 2034355886129515806135191)
                ·
                  refine ⟨3051533829194273709202787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2034355886129515806135191 3051533829194273709202787)
                  ·
                    refine ⟨4577300743791410563804181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3051533829194273709202787 4577300743791410563804181)
                    ·
                      refine ⟨214560972365222370178321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4577300743791410563804181 214560972365222370178321)
                      ·
                        rfl

theorem cell23_417856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 6].length) (baseStart_417856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417856 prefixEnd_417856 := by exact prefixLift 417856
  have htrace : WordTrace (prefixWord ++ tailWord_417856) baseStart_417856 baseEnd_417856 := by
    simpa [prefixWord, tailWord_417856, baseEnd_417856] using wordTrace_append hprefix tailTrace_417856
  have hstable : (prefixWord ++ tailWord_417856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417856).length < 2 ^ (prefixWord ++ tailWord_417856).sum := by decide
  have hdescent : baseEnd_417856 < baseStart_417856 := by decide
  rcases family_descends (prefixWord ++ tailWord_417856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417863 : List Nat := [1, 1, 4, 1, 3, 1, 3, 1, 3, 2, 3]
def baseStart_417863 : Nat := 118140960795 + 417863 * 2 ^ 59
def prefixEnd_417863 : Nat := 4983230072969 + 3 ^ 40 * 417863 * 2
def baseEnd_417863 : Nat := 214564566729803842790789

theorem tailTrace_417863 : CollatzResearch.WordTrace tailWord_417863 prefixEnd_417863 214564566729803842790789 := by
  unfold tailWord_417863
  simp only [CollatzResearch.WordTrace]
  refine ⟨15240715685161191163826243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10160477123440794109217495 15240715685161191163826243)
  ·
    refine ⟨22861073527741786745739365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15240715685161191163826243 22861073527741786745739365)
    ·
      refine ⟨4286451286451585014826131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22861073527741786745739365 4286451286451585014826131)
      ·
        refine ⟨6429676929677377522239197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4286451286451585014826131 6429676929677377522239197)
        ·
          refine ⟨2411128848629016570839699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6429676929677377522239197 2411128848629016570839699)
          ·
            refine ⟨3616693272943524856259549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2411128848629016570839699 3616693272943524856259549)
            ·
              refine ⟨1356259977353821821097331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3616693272943524856259549 1356259977353821821097331)
              ·
                refine ⟨2034389966030732731645997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1356259977353821821097331 2034389966030732731645997)
                ·
                  refine ⟨762896237261524774367249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2034389966030732731645997 762896237261524774367249)
                  ·
                    refine ⟨572172177946143580775437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 762896237261524774367249 572172177946143580775437)
                    ·
                      refine ⟨214564566729803842790789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 572172177946143580775437 214564566729803842790789)
                      ·
                        rfl

theorem cell23_417863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 2, 3].length) (baseStart_417863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417863 prefixEnd_417863 := by exact prefixLift 417863
  have htrace : WordTrace (prefixWord ++ tailWord_417863) baseStart_417863 baseEnd_417863 := by
    simpa [prefixWord, tailWord_417863, baseEnd_417863] using wordTrace_append hprefix tailTrace_417863
  have hstable : (prefixWord ++ tailWord_417863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417863).length < 2 ^ (prefixWord ++ tailWord_417863).sum := by decide
  have hdescent : baseEnd_417863 < baseStart_417863 := by decide
  rcases family_descends (prefixWord ++ tailWord_417863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417910 : List Nat := [5, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3]
def baseStart_417910 : Nat := 118140960795 + 417910 * 2 ^ 59
def prefixEnd_417910 : Nat := 4983230072969 + 3 ^ 40 * 417910 * 2
def baseEnd_417910 : Nat := 214588700320565158903073

theorem tailTrace_417910 : CollatzResearch.WordTrace tailWord_417910 prefixEnd_417910 214588700320565158903073 := by
  unfold tailWord_417910
  simp only [CollatzResearch.WordTrace]
  refine ⟨952651869749432386924199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10161619943993945460524789 952651869749432386924199)
  ·
    refine ⟨1428977804624148580386299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 952651869749432386924199 1428977804624148580386299)
    ·
      refine ⟨2143466706936222870579449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1428977804624148580386299 2143466706936222870579449)
      ·
        refine ⟨1607600030202167152934587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2143466706936222870579449 1607600030202167152934587)
        ·
          refine ⟨2411400045303250729401881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1607600030202167152934587 2411400045303250729401881)
          ·
            refine ⟨1808550033977438047051411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2411400045303250729401881 1808550033977438047051411)
            ·
              refine ⟨2712825050966157070577117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1808550033977438047051411 2712825050966157070577117)
              ·
                refine ⟨1017309394112308901466419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2712825050966157070577117 1017309394112308901466419)
                ·
                  refine ⟨1525964091168463352199629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1017309394112308901466419 1525964091168463352199629)
                  ·
                    refine ⟨572236534188173757074861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1525964091168463352199629 572236534188173757074861)
                    ·
                      refine ⟨214588700320565158903073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 572236534188173757074861 214588700320565158903073)
                      ·
                        rfl

theorem cell23_417910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_417910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417910 prefixEnd_417910 := by exact prefixLift 417910
  have htrace : WordTrace (prefixWord ++ tailWord_417910) baseStart_417910 baseEnd_417910 := by
    simpa [prefixWord, tailWord_417910, baseEnd_417910] using wordTrace_append hprefix tailTrace_417910
  have hstable : (prefixWord ++ tailWord_417910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417910).length < 2 ^ (prefixWord ++ tailWord_417910).sum := by decide
  have hdescent : baseEnd_417910 < baseStart_417910 := by decide
  rcases family_descends (prefixWord ++ tailWord_417910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417920 : List Nat := [2, 1, 1, 2, 1, 3, 1, 6, 1, 3, 2]
def baseStart_417920 : Nat := 118140960795 + 417920 * 2 ^ 59
def prefixEnd_417920 : Nat := 4983230072969 + 3 ^ 40 * 417920 * 2
def baseEnd_417920 : Nat := 214593835127110119778027

theorem tailTrace_417920 : CollatzResearch.WordTrace tailWord_417920 prefixEnd_417920 214593835127110119778027 := by
  unfold tailWord_417920
  simp only [CollatzResearch.WordTrace]
  refine ⟨7621397322977344949325607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10161863097303126599100809 7621397322977344949325607)
  ·
    refine ⟨11432095984466017423988411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7621397322977344949325607 11432095984466017423988411)
    ·
      refine ⟨17148143976699026135982617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11432095984466017423988411 17148143976699026135982617)
      ·
        refine ⟨12861107982524269601986963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17148143976699026135982617 12861107982524269601986963)
        ·
          refine ⟨19291661973786404402980445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12861107982524269601986963 19291661973786404402980445)
          ·
            refine ⟨7234373240169901651117667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19291661973786404402980445 7234373240169901651117667)
            ·
              refine ⟨10851559860254852476676501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7234373240169901651117667 10851559860254852476676501)
              ·
                refine ⟨508666868449446209844211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10851559860254852476676501 508666868449446209844211)
                ·
                  refine ⟨763000302674169314766317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 508666868449446209844211 763000302674169314766317)
                  ·
                    refine ⟨286125113502813493037369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 763000302674169314766317 286125113502813493037369)
                    ·
                      refine ⟨214593835127110119778027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 286125113502813493037369 214593835127110119778027)
                      ·
                        rfl

theorem cell23_417920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 1, 3, 2].length) (baseStart_417920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417920 prefixEnd_417920 := by exact prefixLift 417920
  have htrace : WordTrace (prefixWord ++ tailWord_417920) baseStart_417920 baseEnd_417920 := by
    simpa [prefixWord, tailWord_417920, baseEnd_417920] using wordTrace_append hprefix tailTrace_417920
  have hstable : (prefixWord ++ tailWord_417920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417920).length < 2 ^ (prefixWord ++ tailWord_417920).sum := by decide
  have hdescent : baseEnd_417920 < baseStart_417920 := by decide
  rcases family_descends (prefixWord ++ tailWord_417920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417936 : List Nat := [2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 5]
def baseStart_417936 : Nat := 118140960795 + 417936 * 2 ^ 59
def prefixEnd_417936 : Nat := 4983230072969 + 3 ^ 40 * 417936 * 2
def baseEnd_417936 : Nat := 214602050817582057177953

theorem tailTrace_417936 : CollatzResearch.WordTrace tailWord_417936 prefixEnd_417936 214602050817582057177953 := by
  unfold tailWord_417936
  simp only [CollatzResearch.WordTrace]
  refine ⟨7621689106948362315616831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10162252142597816420822441 7621689106948362315616831)
  ·
    refine ⟨11432533660422543473425247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7621689106948362315616831 11432533660422543473425247)
    ·
      refine ⟨17148800490633815210137871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11432533660422543473425247 17148800490633815210137871)
      ·
        refine ⟨25723200735950722815206807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17148800490633815210137871 25723200735950722815206807)
        ·
          refine ⟨38584801103926084222810211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25723200735950722815206807 38584801103926084222810211)
          ·
            refine ⟨57877201655889126334215317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38584801103926084222810211 57877201655889126334215317)
            ·
              refine ⟨2712993827619802796916343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 57877201655889126334215317 2712993827619802796916343)
              ·
                refine ⟨4069490741429704195374515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2712993827619802796916343 4069490741429704195374515)
                ·
                  refine ⟨6104236112144556293061773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4069490741429704195374515 6104236112144556293061773)
                  ·
                    refine ⟨2289088542054208609898165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6104236112144556293061773 2289088542054208609898165)
                    ·
                      refine ⟨214602050817582057177953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2289088542054208609898165 214602050817582057177953)
                      ·
                        rfl

theorem cell23_417936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 5].length) (baseStart_417936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417936 prefixEnd_417936 := by exact prefixLift 417936
  have htrace : WordTrace (prefixWord ++ tailWord_417936) baseStart_417936 baseEnd_417936 := by
    simpa [prefixWord, tailWord_417936, baseEnd_417936] using wordTrace_append hprefix tailTrace_417936
  have hstable : (prefixWord ++ tailWord_417936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417936).length < 2 ^ (prefixWord ++ tailWord_417936).sum := by decide
  have hdescent : baseEnd_417936 < baseStart_417936 := by decide
  rcases family_descends (prefixWord ++ tailWord_417936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417944 : List Nat := [2, 1, 2, 4, 3, 2, 1, 2, 2, 1, 3]
def baseStart_417944 : Nat := 118140960795 + 417944 * 2 ^ 59
def prefixEnd_417944 : Nat := 4983230072969 + 3 ^ 40 * 417944 * 2
def baseEnd_417944 : Nat := 214606158662818025877917

theorem tailTrace_417944 : CollatzResearch.WordTrace tailWord_417944 prefixEnd_417944 214606158662818025877917 := by
  unfold tailWord_417944
  simp only [CollatzResearch.WordTrace]
  refine ⟨7621834998933870998762443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10162446665245161331683257 7621834998933870998762443)
  ·
    refine ⟨11432752498400806498143665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7621834998933870998762443 11432752498400806498143665)
    ·
      refine ⟨8574564373800604873607749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11432752498400806498143665 8574564373800604873607749)
      ·
        refine ⟨1607730820087613413801453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8574564373800604873607749 1607730820087613413801453)
        ·
          refine ⟨602899057532855030175545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1607730820087613413801453 602899057532855030175545)
          ·
            refine ⟨452174293149641272631659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 602899057532855030175545 452174293149641272631659)
            ·
              refine ⟨678261439724461908947489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 452174293149641272631659 678261439724461908947489)
              ·
                refine ⟨508696079793346431710617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 678261439724461908947489 508696079793346431710617)
                ·
                  refine ⟨381522059845009823782963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 508696079793346431710617 381522059845009823782963)
                  ·
                    refine ⟨572283089767514735674445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 381522059845009823782963 572283089767514735674445)
                    ·
                      refine ⟨214606158662818025877917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 572283089767514735674445 214606158662818025877917)
                      ·
                        rfl

theorem cell23_417944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_417944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_417944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_417944 prefixEnd_417944 := by exact prefixLift 417944
  have htrace : WordTrace (prefixWord ++ tailWord_417944) baseStart_417944 baseEnd_417944 := by
    simpa [prefixWord, tailWord_417944, baseEnd_417944] using wordTrace_append hprefix tailTrace_417944
  have hstable : (prefixWord ++ tailWord_417944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417944).length < 2 ^ (prefixWord ++ tailWord_417944).sum := by decide
  have hdescent : baseEnd_417944 < baseStart_417944 := by decide
  rcases family_descends (prefixWord ++ tailWord_417944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418060 : List Nat := [2, 2, 1, 2, 2, 2, 1, 4, 2, 2, 3]
def baseStart_418060 : Nat := 118140960795 + 418060 * 2 ^ 59
def prefixEnd_418060 : Nat := 4983230072969 + 3 ^ 40 * 418060 * 2
def baseEnd_418060 : Nat := 214665722418739572027383

theorem tailTrace_418060 : CollatzResearch.WordTrace tailWord_418060 prefixEnd_418060 214665722418739572027383 := by
  unfold tailWord_418060
  simp only [CollatzResearch.WordTrace]
  refine ⟨7623950432723746904373817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10165267243631662539165089 7623950432723746904373817)
  ·
    refine ⟨5717962824542810178280363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7623950432723746904373817 5717962824542810178280363)
    ·
      refine ⟨8576944236814215267420545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5717962824542810178280363 8576944236814215267420545)
      ·
        refine ⟨6432708177610661450565409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8576944236814215267420545 6432708177610661450565409)
        ·
          refine ⟨4824531133207996087924057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6432708177610661450565409 4824531133207996087924057)
          ·
            refine ⟨3618398349905997065943043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4824531133207996087924057 3618398349905997065943043)
            ·
              refine ⟨5427597524858995598914565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3618398349905997065943043 5427597524858995598914565)
              ·
                refine ⟨1017674535911061674796481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5427597524858995598914565 1017674535911061674796481)
                ·
                  refine ⟨763255901933296256097361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1017674535911061674796481 763255901933296256097361)
                  ·
                    refine ⟨572441926449972192073021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 763255901933296256097361 572441926449972192073021)
                    ·
                      refine ⟨214665722418739572027383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 572441926449972192073021 214665722418739572027383)
                      ·
                        rfl

theorem cell23_418060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 2, 2, 3].length) (baseStart_418060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418060 prefixEnd_418060 := by exact prefixLift 418060
  have htrace : WordTrace (prefixWord ++ tailWord_418060) baseStart_418060 baseEnd_418060 := by
    simpa [prefixWord, tailWord_418060, baseEnd_418060] using wordTrace_append hprefix tailTrace_418060
  have hstable : (prefixWord ++ tailWord_418060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418060).length < 2 ^ (prefixWord ++ tailWord_418060).sum := by decide
  have hdescent : baseEnd_418060 < baseStart_418060 := by decide
  rcases family_descends (prefixWord ++ tailWord_418060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418080 : List Nat := [2, 1, 1, 5, 2, 1, 2, 3, 6]
def baseStart_418080 : Nat := 118140960795 + 418080 * 2 ^ 59
def prefixEnd_418080 : Nat := 4983230072969 + 3 ^ 40 * 418080 * 2
def baseEnd_418080 : Nat := 23852888003536610419699

theorem tailTrace_418080 : CollatzResearch.WordTrace tailWord_418080 prefixEnd_418080 23852888003536610419699 := by
  unfold tailWord_418080
  simp only [CollatzResearch.WordTrace]
  refine ⟨7624315162687518612237847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10165753550250024816317129 7624315162687518612237847)
  ·
    refine ⟨11436472744031277918356771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7624315162687518612237847 11436472744031277918356771)
    ·
      refine ⟨17154709116046916877535157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11436472744031277918356771 17154709116046916877535157)
      ·
        refine ⟨1608253979629398457268921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17154709116046916877535157 1608253979629398457268921)
        ·
          refine ⟨1206190484722048842951691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1608253979629398457268921 1206190484722048842951691)
          ·
            refine ⟨1809285727083073264427537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1206190484722048842951691 1809285727083073264427537)
            ·
              refine ⟨1356964295312304948320653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1809285727083073264427537 1356964295312304948320653)
              ·
                refine ⟨508861610742114355620245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1356964295312304948320653 508861610742114355620245)
                ·
                  refine ⟨23852888003536610419699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 508861610742114355620245 23852888003536610419699)
                  ·
                    rfl

theorem cell23_418080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 6].length) (baseStart_418080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418080 prefixEnd_418080 := by exact prefixLift 418080
  have htrace : WordTrace (prefixWord ++ tailWord_418080) baseStart_418080 baseEnd_418080 := by
    simpa [prefixWord, tailWord_418080, baseEnd_418080] using wordTrace_append hprefix tailTrace_418080
  have hstable : (prefixWord ++ tailWord_418080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418080).length < 2 ^ (prefixWord ++ tailWord_418080).sum := by decide
  have hdescent : baseEnd_418080 < baseStart_418080 := by decide
  rcases family_descends (prefixWord ++ tailWord_418080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418094 : List Nat := [4, 1, 3, 3, 1, 1, 1, 1, 1, 4, 3]
def baseStart_418094 : Nat := 118140960795 + 418094 * 2 ^ 59
def prefixEnd_418094 : Nat := 4983230072969 + 3 ^ 40 * 418094 * 2
def baseEnd_418094 : Nat := 214683180760992439002227

theorem tailTrace_418094 : CollatzResearch.WordTrace tailWord_418094 prefixEnd_418094 214683180760992439002227 := by
  unfold tailWord_418094
  simp only [CollatzResearch.WordTrace]
  refine ⟨1906142618415539701935667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10166093964882878410323557 1906142618415539701935667)
  ·
    refine ⟨2859213927623309552903501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1906142618415539701935667 2859213927623309552903501)
    ·
      refine ⟨1072205222858741082338813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2859213927623309552903501 1072205222858741082338813)
      ·
        refine ⟨402076958572027905877055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1072205222858741082338813 402076958572027905877055)
        ·
          refine ⟨603115437858041858815583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402076958572027905877055 603115437858041858815583)
          ·
            refine ⟨904673156787062788223375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 603115437858041858815583 904673156787062788223375)
            ·
              refine ⟨1357009735180594182335063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 904673156787062788223375 1357009735180594182335063)
              ·
                refine ⟨2035514602770891273502595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1357009735180594182335063 2035514602770891273502595)
                ·
                  refine ⟨3053271904156336910253893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2035514602770891273502595 3053271904156336910253893)
                  ·
                    refine ⟨572488482029313170672605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3053271904156336910253893 572488482029313170672605)
                    ·
                      refine ⟨214683180760992439002227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 572488482029313170672605 214683180760992439002227)
                      ·
                        rfl

theorem cell23_418094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_418094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418094 prefixEnd_418094 := by exact prefixLift 418094
  have htrace : WordTrace (prefixWord ++ tailWord_418094) baseStart_418094 baseEnd_418094 := by
    simpa [prefixWord, tailWord_418094, baseEnd_418094] using wordTrace_append hprefix tailTrace_418094
  have hstable : (prefixWord ++ tailWord_418094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418094).length < 2 ^ (prefixWord ++ tailWord_418094).sum := by decide
  have hdescent : baseEnd_418094 < baseStart_418094 := by decide
  rcases family_descends (prefixWord ++ tailWord_418094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418124 : List Nat := [2, 2, 1, 3, 2, 1, 1, 6, 1, 1, 3]
def baseStart_418124 : Nat := 118140960795 + 418124 * 2 ^ 59
def prefixEnd_418124 : Nat := 4983230072969 + 3 ^ 40 * 418124 * 2
def baseEnd_418124 : Nat := 214698585180627321627089

theorem tailTrace_418124 : CollatzResearch.WordTrace tailWord_418124 prefixEnd_418124 214698585180627321627089 := by
  unfold tailWord_418124
  simp only [CollatzResearch.WordTrace]
  refine ⟨7625117568607816369538713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10166823424810421826051617 7625117568607816369538713)
  ·
    refine ⟨5718838176455862277154035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7625117568607816369538713 5718838176455862277154035)
    ·
      refine ⟨8578257264683793415731053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5718838176455862277154035 8578257264683793415731053)
      ·
        refine ⟨3216846474256422530899145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8578257264683793415731053 3216846474256422530899145)
        ·
          refine ⟨2412634855692316898174359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3216846474256422530899145 2412634855692316898174359)
          ·
            refine ⟨3618952283538475347261539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2412634855692316898174359 3618952283538475347261539)
            ·
              refine ⟨5428428425307713020892309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3618952283538475347261539 5428428425307713020892309)
              ·
                refine ⟨254457582436299047854327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5428428425307713020892309 254457582436299047854327)
                ·
                  refine ⟨381686373654448571781491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 254457582436299047854327 381686373654448571781491)
                  ·
                    refine ⟨572529560481672857672237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 381686373654448571781491 572529560481672857672237)
                    ·
                      refine ⟨214698585180627321627089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 572529560481672857672237 214698585180627321627089)
                      ·
                        rfl

theorem cell23_418124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 6, 1, 1, 3].length) (baseStart_418124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418124 prefixEnd_418124 := by exact prefixLift 418124
  have htrace : WordTrace (prefixWord ++ tailWord_418124) baseStart_418124 baseEnd_418124 := by
    simpa [prefixWord, tailWord_418124, baseEnd_418124] using wordTrace_append hprefix tailTrace_418124
  have hstable : (prefixWord ++ tailWord_418124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418124).length < 2 ^ (prefixWord ++ tailWord_418124).sum := by decide
  have hdescent : baseEnd_418124 < baseStart_418124 := by decide
  rcases family_descends (prefixWord ++ tailWord_418124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418130 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4]
def baseStart_418130 : Nat := 118140960795 + 418130 * 2 ^ 59
def prefixEnd_418130 : Nat := 4983230072969 + 3 ^ 40 * 418130 * 2
def baseEnd_418130 : Nat := 214701666064554298152061

theorem tailTrace_418130 : CollatzResearch.WordTrace tailWord_418130 prefixEnd_418130 214701666064554298152061 := by
  unfold tailWord_418130
  simp only [CollatzResearch.WordTrace]
  refine ⟨3812613493798473940948961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10166969316795930509197229 3812613493798473940948961)
  ·
    refine ⟨2859460120348855455711721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3812613493798473940948961 2859460120348855455711721)
    ·
      refine ⟨2144595090261641591783791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2859460120348855455711721 2144595090261641591783791)
      ·
        refine ⟨3216892635392462387675687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2144595090261641591783791 3216892635392462387675687)
        ·
          refine ⟨4825338953088693581513531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3216892635392462387675687 4825338953088693581513531)
          ·
            refine ⟨7238008429633040372270297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4825338953088693581513531 7238008429633040372270297)
            ·
              refine ⟨5428506322224780279202723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7238008429633040372270297 5428506322224780279202723)
              ·
                refine ⟨8142759483337170418804085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5428506322224780279202723 8142759483337170418804085)
                ·
                  refine ⟨763383701562859726762883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8142759483337170418804085 763383701562859726762883)
                  ·
                    refine ⟨1145075552344289590144325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 763383701562859726762883 1145075552344289590144325)
                    ·
                      refine ⟨214701666064554298152061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1145075552344289590144325 214701666064554298152061)
                      ·
                        rfl

theorem cell23_418130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_418130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418130 prefixEnd_418130 := by exact prefixLift 418130
  have htrace : WordTrace (prefixWord ++ tailWord_418130) baseStart_418130 baseEnd_418130 := by
    simpa [prefixWord, tailWord_418130, baseEnd_418130] using wordTrace_append hprefix tailTrace_418130
  have hstable : (prefixWord ++ tailWord_418130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418130).length < 2 ^ (prefixWord ++ tailWord_418130).sum := by decide
  have hdescent : baseEnd_418130 < baseStart_418130 := by decide
  rcases family_descends (prefixWord ++ tailWord_418130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418147 : List Nat := [1, 1, 1, 5, 2, 1, 4, 2, 1, 1, 4]
def baseStart_418147 : Nat := 118140960795 + 418147 * 2 ^ 59
def prefixEnd_418147 : Nat := 4983230072969 + 3 ^ 40 * 418147 * 2
def baseEnd_418147 : Nat := 214710395235680731639483

theorem tailTrace_418147 : CollatzResearch.WordTrace tailWord_418147 prefixEnd_418147 214710395235680731639483 := by
  unfold tailWord_418147
  simp only [CollatzResearch.WordTrace]
  refine ⟨15251074016132307667164695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10167382677421538444776463 15251074016132307667164695)
  ·
    refine ⟨22876611024198461500747043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15251074016132307667164695 22876611024198461500747043)
    ·
      refine ⟨34314916536297692251120565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22876611024198461500747043 34314916536297692251120565)
      ·
        refine ⟨3217023425277908648542553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34314916536297692251120565 3217023425277908648542553)
        ·
          refine ⟨2412767568958431486406915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3217023425277908648542553 2412767568958431486406915)
          ·
            refine ⟨3619151353437647229610373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2412767568958431486406915 3619151353437647229610373)
            ·
              refine ⟨678590878769558855551945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3619151353437647229610373 678590878769558855551945)
              ·
                refine ⟨508943159077169141663959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 678590878769558855551945 508943159077169141663959)
                ·
                  refine ⟨763414738615753712495939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 508943159077169141663959 763414738615753712495939)
                  ·
                    refine ⟨1145122107923630568743909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 763414738615753712495939 1145122107923630568743909)
                    ·
                      refine ⟨214710395235680731639483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1145122107923630568743909 214710395235680731639483)
                      ·
                        rfl

theorem cell23_418147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_418147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418147 prefixEnd_418147 := by exact prefixLift 418147
  have htrace : WordTrace (prefixWord ++ tailWord_418147) baseStart_418147 baseEnd_418147 := by
    simpa [prefixWord, tailWord_418147, baseEnd_418147] using wordTrace_append hprefix tailTrace_418147
  have hstable : (prefixWord ++ tailWord_418147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418147).length < 2 ^ (prefixWord ++ tailWord_418147).sum := by decide
  have hdescent : baseEnd_418147 < baseStart_418147 := by decide
  rcases family_descends (prefixWord ++ tailWord_418147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418153 : List Nat := [1, 2, 1, 1, 1, 3, 5, 9]
def baseStart_418153 : Nat := 118140960795 + 418153 * 2 ^ 59
def prefixEnd_418153 : Nat := 4983230072969 + 3 ^ 40 * 418153 * 2
def baseEnd_418153 : Nat := 7952350967392878080165

theorem tailTrace_418153 : CollatzResearch.WordTrace tailWord_418153 prefixEnd_418153 7952350967392878080165 := by
  unfold tailWord_418153
  simp only [CollatzResearch.WordTrace]
  refine ⟨15251292854110570691883113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10167528569407047127922075 15251292854110570691883113)
  ·
    refine ⟨11438469640582928018912335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15251292854110570691883113 11438469640582928018912335)
    ·
      refine ⟨17157704460874392028368503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11438469640582928018912335 17157704460874392028368503)
      ·
        refine ⟨25736556691311588042552755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17157704460874392028368503 25736556691311588042552755)
        ·
          refine ⟨38604835036967382063829133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25736556691311588042552755 38604835036967382063829133)
          ·
            refine ⟨14476813138862768273935925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38604835036967382063829133 14476813138862768273935925)
            ·
              refine ⟨1357201231768384525681493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14476813138862768273935925 1357201231768384525681493)
              ·
                refine ⟨7952350967392878080165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1357201231768384525681493 7952350967392878080165)
                ·
                  rfl

theorem cell23_418153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 9].length) (baseStart_418153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418153 prefixEnd_418153 := by exact prefixLift 418153
  have htrace : WordTrace (prefixWord ++ tailWord_418153) baseStart_418153 baseEnd_418153 := by
    simpa [prefixWord, tailWord_418153, baseEnd_418153] using wordTrace_append hprefix tailTrace_418153
  have hstable : (prefixWord ++ tailWord_418153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418153).length < 2 ^ (prefixWord ++ tailWord_418153).sum := by decide
  have hdescent : baseEnd_418153 < baseStart_418153 := by decide
  rcases family_descends (prefixWord ++ tailWord_418153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418198 : List Nat := [5, 3, 1, 2, 1, 1, 1, 1, 3, 1, 4]
def baseStart_418198 : Nat := 118140960795 + 418198 * 2 ^ 59
def prefixEnd_418198 : Nat := 4983230072969 + 3 ^ 40 * 418198 * 2
def baseEnd_418198 : Nat := 214736582749060032101749

theorem tailTrace_418198 : CollatzResearch.WordTrace tailWord_418198 prefixEnd_418198 214736582749060032101749 := by
  unfold tailWord_418198
  simp only [CollatzResearch.WordTrace]
  refine ⟨953308383684221461079453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10168622759298362251514165 953308383684221461079453)
  ·
    refine ⟨357490643881583047904795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 953308383684221461079453 357490643881583047904795)
    ·
      refine ⟨536235965822374571857193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357490643881583047904795 536235965822374571857193)
      ·
        refine ⟨402176974366780928892895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 536235965822374571857193 402176974366780928892895)
        ·
          refine ⟨603265461550171393339343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402176974366780928892895 603265461550171393339343)
          ·
            refine ⟨904898192325257090009015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 603265461550171393339343 904898192325257090009015)
            ·
              refine ⟨1357347288487885635013523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 904898192325257090009015 1357347288487885635013523)
              ·
                refine ⟨2036020932731828452520285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1357347288487885635013523 2036020932731828452520285)
                ·
                  refine ⟨763507849774435669695107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2036020932731828452520285 763507849774435669695107)
                  ·
                    refine ⟨1145261774661653504542661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 763507849774435669695107 1145261774661653504542661)
                    ·
                      refine ⟨214736582749060032101749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1145261774661653504542661 214736582749060032101749)
                      ·
                        rfl

theorem cell23_418198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_418198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418198 prefixEnd_418198 := by exact prefixLift 418198
  have htrace : WordTrace (prefixWord ++ tailWord_418198) baseStart_418198 baseEnd_418198 := by
    simpa [prefixWord, tailWord_418198, baseEnd_418198] using wordTrace_append hprefix tailTrace_418198
  have hstable : (prefixWord ++ tailWord_418198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418198).length < 2 ^ (prefixWord ++ tailWord_418198).sum := by decide
  have hdescent : baseEnd_418198 < baseStart_418198 := by decide
  rcases family_descends (prefixWord ++ tailWord_418198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418218 : List Nat := [3, 1, 6, 1, 1, 2, 1, 1, 1, 1, 5]
def baseStart_418218 : Nat := 118140960795 + 418218 * 2 ^ 59
def prefixEnd_418218 : Nat := 4983230072969 + 3 ^ 40 * 418218 * 2
def baseEnd_418218 : Nat := 214746852362149953851657

theorem tailTrace_418218 : CollatzResearch.WordTrace tailWord_418218 prefixEnd_418218 214746852362149953851657 := by
  unfold tailWord_418218
  simp only [CollatzResearch.WordTrace]
  refine ⟨3813415899718771698249827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10169109065916724528666205 3813415899718771698249827)
  ·
    refine ⟨5720123849578157547374741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3813415899718771698249827 5720123849578157547374741)
    ·
      refine ⟨268130805448976135033191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5720123849578157547374741 268130805448976135033191)
      ·
        refine ⟨402196208173464202549787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268130805448976135033191 402196208173464202549787)
        ·
          refine ⟨603294312260196303824681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402196208173464202549787 603294312260196303824681)
          ·
            refine ⟨452470734195147227868511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 603294312260196303824681 452470734195147227868511)
            ·
              refine ⟨678706101292720841802767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 452470734195147227868511 678706101292720841802767)
              ·
                refine ⟨1018059151939081262704151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 678706101292720841802767 1018059151939081262704151)
                ·
                  refine ⟨1527088727908621894056227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1018059151939081262704151 1527088727908621894056227)
                  ·
                    refine ⟨2290633091862932841084341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1527088727908621894056227 2290633091862932841084341)
                    ·
                      refine ⟨214746852362149953851657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2290633091862932841084341 214746852362149953851657)
                      ·
                        rfl

theorem cell23_418218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_418218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418218 prefixEnd_418218 := by exact prefixLift 418218
  have htrace : WordTrace (prefixWord ++ tailWord_418218) baseStart_418218 baseEnd_418218 := by
    simpa [prefixWord, tailWord_418218, baseEnd_418218] using wordTrace_append hprefix tailTrace_418218
  have hstable : (prefixWord ++ tailWord_418218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418218).length < 2 ^ (prefixWord ++ tailWord_418218).sum := by decide
  have hdescent : baseEnd_418218 < baseStart_418218 := by decide
  rcases family_descends (prefixWord ++ tailWord_418218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418254 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2]
def baseStart_418254 : Nat := 118140960795 + 418254 * 2 ^ 59
def prefixEnd_418254 : Nat := 4983230072969 + 3 ^ 40 * 418254 * 2
def baseEnd_418254 : Nat := 214765337665711813001491

theorem tailTrace_418254 : CollatzResearch.WordTrace tailWord_418254 prefixEnd_418254 214765337665711813001491 := by
  unfold tailWord_418254
  simp only [CollatzResearch.WordTrace]
  refine ⟨1906872078343083117663727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10169984417829776627539877 1906872078343083117663727)
  ·
    refine ⟨2860308117514624676495591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1906872078343083117663727 2860308117514624676495591)
    ·
      refine ⟨4290462176271937014743387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2860308117514624676495591 4290462176271937014743387)
      ·
        refine ⟨6435693264407905522115081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4290462176271937014743387 6435693264407905522115081)
        ·
          refine ⟨4826769948305929141586311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6435693264407905522115081 4826769948305929141586311)
          ·
            refine ⟨7240154922458893712379467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4826769948305929141586311 7240154922458893712379467)
            ·
              refine ⟨10860232383688340568569201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7240154922458893712379467 10860232383688340568569201)
              ·
                refine ⟨8145174287766255426426901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10860232383688340568569201 8145174287766255426426901)
                ·
                  refine ⟨381805044739043223113761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8145174287766255426426901 381805044739043223113761)
                  ·
                    refine ⟨286353783554282417335321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 381805044739043223113761 286353783554282417335321)
                    ·
                      refine ⟨214765337665711813001491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 286353783554282417335321 214765337665711813001491)
                      ·
                        rfl

theorem cell23_418254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2].length) (baseStart_418254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418254 prefixEnd_418254 := by exact prefixLift 418254
  have htrace : WordTrace (prefixWord ++ tailWord_418254) baseStart_418254 baseEnd_418254 := by
    simpa [prefixWord, tailWord_418254, baseEnd_418254] using wordTrace_append hprefix tailTrace_418254
  have hstable : (prefixWord ++ tailWord_418254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418254).length < 2 ^ (prefixWord ++ tailWord_418254).sum := by decide
  have hdescent : baseEnd_418254 < baseStart_418254 := by decide
  rcases family_descends (prefixWord ++ tailWord_418254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418275 : List Nat := [1, 1, 1, 6, 4, 1, 2, 1, 1, 3, 2]
def baseStart_418275 : Nat := 118140960795 + 418275 * 2 ^ 59
def prefixEnd_418275 : Nat := 4983230072969 + 3 ^ 40 * 418275 * 2
def baseEnd_418275 : Nat := 214776120759456230838895

theorem tailTrace_418275 : CollatzResearch.WordTrace tailWord_418275 prefixEnd_418275 214776120759456230838895 := by
  unfold tailWord_418275
  simp only [CollatzResearch.WordTrace]
  refine ⟨15255742559668585527824279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10170495039779057018549519 15255742559668585527824279)
  ·
    refine ⟨22883613839502878291736419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15255742559668585527824279 22883613839502878291736419)
    ·
      refine ⟨34325420759254317437604629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22883613839502878291736419 34325420759254317437604629)
      ·
        refine ⟨1609004098090046129887717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34325420759254317437604629 1609004098090046129887717)
        ·
          refine ⟨301688268391883649353947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1609004098090046129887717 301688268391883649353947)
          ·
            refine ⟨452532402587825474030921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301688268391883649353947 452532402587825474030921)
            ·
              refine ⟨339399301940869105523191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 452532402587825474030921 339399301940869105523191)
              ·
                refine ⟨509098952911303658284787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 339399301940869105523191 509098952911303658284787)
                ·
                  refine ⟨763648429366955487427181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 509098952911303658284787 763648429366955487427181)
                  ·
                    refine ⟨286368161012608307785193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 763648429366955487427181 286368161012608307785193)
                    ·
                      refine ⟨214776120759456230838895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 286368161012608307785193 214776120759456230838895)
                      ·
                        rfl

theorem cell23_418275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_418275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418275 prefixEnd_418275 := by exact prefixLift 418275
  have htrace : WordTrace (prefixWord ++ tailWord_418275) baseStart_418275 baseEnd_418275 := by
    simpa [prefixWord, tailWord_418275, baseEnd_418275] using wordTrace_append hprefix tailTrace_418275
  have hstable : (prefixWord ++ tailWord_418275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418275).length < 2 ^ (prefixWord ++ tailWord_418275).sum := by decide
  have hdescent : baseEnd_418275 < baseStart_418275 := by decide
  rcases family_descends (prefixWord ++ tailWord_418275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418294 : List Nat := [5, 1, 1, 1, 2, 1, 1, 6, 5]
def baseStart_418294 : Nat := 118140960795 + 418294 * 2 ^ 59
def prefixEnd_418294 : Nat := 4983230072969 + 3 ^ 40 * 418294 * 2
def baseEnd_418294 : Nat := 23865097432432406277923

theorem tailTrace_418294 : CollatzResearch.WordTrace tailWord_418294 prefixEnd_418294 23865097432432406277923 := by
  unfold tailWord_418294
  simp only [CollatzResearch.WordTrace]
  refine ⟨953527221662484485797871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10170957031066501181843957 953527221662484485797871)
  ·
    refine ⟨1430290832493726728696807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 953527221662484485797871 1430290832493726728696807)
    ·
      refine ⟨2145436248740590093045211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1430290832493726728696807 2145436248740590093045211)
      ·
        refine ⟨3218154373110885139567817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2145436248740590093045211 3218154373110885139567817)
        ·
          refine ⟨2413615779833163854675863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3218154373110885139567817 2413615779833163854675863)
          ·
            refine ⟨3620423669749745782013795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2413615779833163854675863 3620423669749745782013795)
            ·
              refine ⟨5430635504624618673020693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3620423669749745782013795 5430635504624618673020693)
              ·
                refine ⟨254561039279279000297845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5430635504624618673020693 254561039279279000297845)
                ·
                  refine ⟨23865097432432406277923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 254561039279279000297845 23865097432432406277923)
                  ·
                    rfl

theorem cell23_418294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_418294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418294 prefixEnd_418294 := by exact prefixLift 418294
  have htrace : WordTrace (prefixWord ++ tailWord_418294) baseStart_418294 baseEnd_418294 := by
    simpa [prefixWord, tailWord_418294, baseEnd_418294] using wordTrace_append hprefix tailTrace_418294
  have hstable : (prefixWord ++ tailWord_418294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418294).length < 2 ^ (prefixWord ++ tailWord_418294).sum := by decide
  have hdescent : baseEnd_418294 < baseStart_418294 := by decide
  rcases family_descends (prefixWord ++ tailWord_418294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418297 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 1, 7, 2]
def baseStart_418297 : Nat := 118140960795 + 418297 * 2 ^ 59
def prefixEnd_418297 : Nat := 4983230072969 + 3 ^ 40 * 418297 * 2
def baseEnd_418297 : Nat := 214787417333855144763793

theorem tailTrace_418297 : CollatzResearch.WordTrace tailWord_418297 prefixEnd_418297 214787417333855144763793 := by
  unfold tailWord_418297
  simp only [CollatzResearch.WordTrace]
  refine ⟨15256544965588883285125145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10171029977059255523416763 15256544965588883285125145)
  ·
    refine ⟨11442408724191662463843859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15256544965588883285125145 11442408724191662463843859)
    ·
      refine ⟨17163613086287493695765789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11442408724191662463843859 17163613086287493695765789)
      ·
        refine ⟨6436354907357810135912171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17163613086287493695765789 6436354907357810135912171)
        ·
          refine ⟨9654532361036715203868257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6436354907357810135912171 9654532361036715203868257)
          ·
            refine ⟨7240899270777536402901193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9654532361036715203868257 7240899270777536402901193)
            ·
              refine ⟨5430674453083152302175895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7240899270777536402901193 5430674453083152302175895)
              ·
                refine ⟨8146011679624728453263843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5430674453083152302175895 8146011679624728453263843)
                ·
                  refine ⟨12219017519437092679895765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8146011679624728453263843 12219017519437092679895765)
                  ·
                    refine ⟨286383223111806859685057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12219017519437092679895765 286383223111806859685057)
                    ·
                      refine ⟨214787417333855144763793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 286383223111806859685057 214787417333855144763793)
                      ·
                        rfl

theorem cell23_418297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 7, 2].length) (baseStart_418297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418297 prefixEnd_418297 := by exact prefixLift 418297
  have htrace : WordTrace (prefixWord ++ tailWord_418297) baseStart_418297 baseEnd_418297 := by
    simpa [prefixWord, tailWord_418297, baseEnd_418297] using wordTrace_append hprefix tailTrace_418297
  have hstable : (prefixWord ++ tailWord_418297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418297).length < 2 ^ (prefixWord ++ tailWord_418297).sum := by decide
  have hdescent : baseEnd_418297 < baseStart_418297 := by decide
  rcases family_descends (prefixWord ++ tailWord_418297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418300 : List Nat := [2, 2, 2, 1, 2, 1, 1, 3, 1, 1, 7]
def baseStart_418300 : Nat := 118140960795 + 418300 * 2 ^ 59
def prefixEnd_418300 : Nat := 4983230072969 + 3 ^ 40 * 418300 * 2
def baseEnd_418300 : Nat := 214788957775818633026279

theorem tailTrace_418300 : CollatzResearch.WordTrace tailWord_418300 prefixEnd_418300 214788957775818633026279 := by
  unfold tailWord_418300
  simp only [CollatzResearch.WordTrace]
  refine ⟨7628327192289007398742177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10171102923052009864989569 7628327192289007398742177)
  ·
    refine ⟨5721245394216755549056633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7628327192289007398742177 5721245394216755549056633)
    ·
      refine ⟨4290934045662566661792475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5721245394216755549056633 4290934045662566661792475)
      ·
        refine ⟨6436401068493849992688713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4290934045662566661792475 6436401068493849992688713)
        ·
          refine ⟨4827300801370387494516535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6436401068493849992688713 4827300801370387494516535)
          ·
            refine ⟨7240951202055581241774803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4827300801370387494516535 7240951202055581241774803)
            ·
              refine ⟨10861426803083371862662205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7240951202055581241774803 10861426803083371862662205)
              ·
                refine ⟨4073035051156264448498327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10861426803083371862662205 4073035051156264448498327)
                ·
                  refine ⟨6109552576734396672747491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4073035051156264448498327 6109552576734396672747491)
                  ·
                    refine ⟨9164328865101595009121237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6109552576734396672747491 9164328865101595009121237)
                    ·
                      refine ⟨214788957775818633026279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 9164328865101595009121237 214788957775818633026279)
                      ·
                        rfl

theorem cell23_418300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_418300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418300 prefixEnd_418300 := by exact prefixLift 418300
  have htrace : WordTrace (prefixWord ++ tailWord_418300) baseStart_418300 baseEnd_418300 := by
    simpa [prefixWord, tailWord_418300, baseEnd_418300] using wordTrace_append hprefix tailTrace_418300
  have hstable : (prefixWord ++ tailWord_418300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418300).length < 2 ^ (prefixWord ++ tailWord_418300).sum := by decide
  have hdescent : baseEnd_418300 < baseStart_418300 := by decide
  rcases family_descends (prefixWord ++ tailWord_418300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418324 : List Nat := [2, 4, 3, 1, 1, 1, 2, 1, 1, 7]
def baseStart_418324 : Nat := 118140960795 + 418324 * 2 ^ 59
def prefixEnd_418324 : Nat := 4983230072969 + 3 ^ 40 * 418324 * 2
def baseEnd_418324 : Nat := 71600427103842179708723

theorem tailTrace_418324 : CollatzResearch.WordTrace tailWord_418324 prefixEnd_418324 71600427103842179708723 := by
  unfold tailWord_418324
  simp only [CollatzResearch.WordTrace]
  refine ⟨7628764868245533448179013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10171686490994044597572017 7628764868245533448179013)
  ·
    refine ⟨1430393412796037521533565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7628764868245533448179013 1430393412796037521533565)
    ·
      refine ⟨536397529798514070575087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1430393412796037521533565 536397529798514070575087)
      ·
        refine ⟨804596294697771105862631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 536397529798514070575087 804596294697771105862631)
        ·
          refine ⟨1206894442046656658793947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 804596294697771105862631 1206894442046656658793947)
          ·
            refine ⟨1810341663069984988190921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1206894442046656658793947 1810341663069984988190921)
            ·
              refine ⟨1357756247302488741143191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1810341663069984988190921 1357756247302488741143191)
              ·
                refine ⟨2036634370953733111714787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1357756247302488741143191 2036634370953733111714787)
                ·
                  refine ⟨3054951556430599667572181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2036634370953733111714787 3054951556430599667572181)
                  ·
                    refine ⟨71600427103842179708723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3054951556430599667572181 71600427103842179708723)
                    ·
                      rfl

theorem cell23_418324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_418324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418324 prefixEnd_418324 := by exact prefixLift 418324
  have htrace : WordTrace (prefixWord ++ tailWord_418324) baseStart_418324 baseEnd_418324 := by
    simpa [prefixWord, tailWord_418324, baseEnd_418324] using wordTrace_append hprefix tailTrace_418324
  have hstable : (prefixWord ++ tailWord_418324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418324).length < 2 ^ (prefixWord ++ tailWord_418324).sum := by decide
  have hdescent : baseEnd_418324 < baseStart_418324 := by decide
  rcases family_descends (prefixWord ++ tailWord_418324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418344 : List Nat := [2, 1, 5, 2, 1, 1, 1, 1, 4, 1, 4]
def baseStart_418344 : Nat := 118140960795 + 418344 * 2 ^ 59
def prefixEnd_418344 : Nat := 4983230072969 + 3 ^ 40 * 418344 * 2
def baseEnd_418344 : Nat := 214811550924616460876077

theorem tailTrace_418344 : CollatzResearch.WordTrace tailWord_418344 prefixEnd_418344 214811550924616460876077 := by
  unfold tailWord_418344
  simp only [CollatzResearch.WordTrace]
  refine ⟨7629129598209305156043043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10172172797612406874724057 7629129598209305156043043)
  ·
    refine ⟨11443694397313957734064565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7629129598209305156043043 11443694397313957734064565)
    ·
      refine ⟨1072846349748183537568553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11443694397313957734064565 1072846349748183537568553)
      ·
        refine ⟨804634762311137653176415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1072846349748183537568553 804634762311137653176415)
        ·
          refine ⟨1206952143466706479764623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 804634762311137653176415 1206952143466706479764623)
          ·
            refine ⟨1810428215200059719646935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1206952143466706479764623 1810428215200059719646935)
            ·
              refine ⟨2715642322800089579470403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1810428215200059719646935 2715642322800089579470403)
              ·
                refine ⟨4073463484200134369205605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2715642322800089579470403 4073463484200134369205605)
                ·
                  refine ⟨763774403287525194226051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4073463484200134369205605 763774403287525194226051)
                  ·
                    refine ⟨1145661604931287791339077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 763774403287525194226051 1145661604931287791339077)
                    ·
                      refine ⟨214811550924616460876077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1145661604931287791339077 214811550924616460876077)
                      ·
                        rfl

theorem cell23_418344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_418344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418344 prefixEnd_418344 := by exact prefixLift 418344
  have htrace : WordTrace (prefixWord ++ tailWord_418344) baseStart_418344 baseEnd_418344 := by
    simpa [prefixWord, tailWord_418344, baseEnd_418344] using wordTrace_append hprefix tailTrace_418344
  have hstable : (prefixWord ++ tailWord_418344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418344).length < 2 ^ (prefixWord ++ tailWord_418344).sum := by decide
  have hdescent : baseEnd_418344 < baseStart_418344 := by decide
  rcases family_descends (prefixWord ++ tailWord_418344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418354 : List Nat := [3, 2, 1, 1, 2, 1, 5, 1, 3, 4]
def baseStart_418354 : Nat := 118140960795 + 418354 * 2 ^ 59
def prefixEnd_418354 : Nat := 4983230072969 + 3 ^ 40 * 418354 * 2
def baseEnd_418354 : Nat := 71605561910387140583677

theorem tailTrace_418354 : CollatzResearch.WordTrace tailWord_418354 prefixEnd_418354 71605561910387140583677 := by
  unfold tailWord_418354
  simp only [CollatzResearch.WordTrace]
  refine ⟨3814655981595595504987529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10172415950921588013300077 3814655981595595504987529)
  ·
    refine ⟨2860991986196696628740647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3814655981595595504987529 2860991986196696628740647)
    ·
      refine ⟨4291487979295044943110971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2860991986196696628740647 4291487979295044943110971)
      ·
        refine ⟨6437231968942567414666457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4291487979295044943110971 6437231968942567414666457)
        ·
          refine ⟨4827923976706925560999843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6437231968942567414666457 4827923976706925560999843)
          ·
            refine ⟨7241885965060388341499765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4827923976706925560999843 7241885965060388341499765)
            ·
              refine ⟨678926809224411407015603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7241885965060388341499765 678926809224411407015603)
              ·
                refine ⟨1018390213836617110523405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 678926809224411407015603 1018390213836617110523405)
                ·
                  refine ⟨381896330188731416446277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1018390213836617110523405 381896330188731416446277)
                  ·
                    refine ⟨71605561910387140583677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 381896330188731416446277 71605561910387140583677)
                    ·
                      rfl

theorem cell23_418354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 3, 4].length) (baseStart_418354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418354 prefixEnd_418354 := by exact prefixLift 418354
  have htrace : WordTrace (prefixWord ++ tailWord_418354) baseStart_418354 baseEnd_418354 := by
    simpa [prefixWord, tailWord_418354, baseEnd_418354] using wordTrace_append hprefix tailTrace_418354
  have hstable : (prefixWord ++ tailWord_418354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418354).length < 2 ^ (prefixWord ++ tailWord_418354).sum := by decide
  have hdescent : baseEnd_418354 < baseStart_418354 := by decide
  rcases family_descends (prefixWord ++ tailWord_418354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418367 : List Nat := [1, 1, 2, 2, 3, 2, 3, 3, 6]
def baseStart_418367 : Nat := 118140960795 + 418367 * 2 ^ 59
def prefixEnd_418367 : Nat := 4983230072969 + 3 ^ 40 * 418367 * 2
def baseEnd_418367 : Nat := 23869262331074430098719

theorem tailTrace_418367 : CollatzResearch.WordTrace tailWord_418367 prefixEnd_418367 23869262331074430098719 := by
  unfold tailWord_418367
  simp only [CollatzResearch.WordTrace]
  refine ⟨15259098075335285240173355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10172732050223523493448903 15259098075335285240173355)
  ·
    refine ⟨22888647113002927860260033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15259098075335285240173355 22888647113002927860260033)
    ·
      refine ⟨17166485334752195895195025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22888647113002927860260033 17166485334752195895195025)
      ·
        refine ⟨12874864001064146921396269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17166485334752195895195025 12874864001064146921396269)
        ·
          refine ⟨4828074000399055095523601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12874864001064146921396269 4828074000399055095523601)
          ·
            refine ⟨3621055500299291321642701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4828074000399055095523601 3621055500299291321642701)
            ·
              refine ⟨1357895812612234245616013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3621055500299291321642701 1357895812612234245616013)
              ·
                refine ⟨509210929729587842106005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1357895812612234245616013 509210929729587842106005)
                ·
                  refine ⟨23869262331074430098719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 509210929729587842106005 23869262331074430098719)
                  ·
                    rfl

theorem cell23_418367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 6].length) (baseStart_418367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418367 prefixEnd_418367 := by exact prefixLift 418367
  have htrace : WordTrace (prefixWord ++ tailWord_418367) baseStart_418367 baseEnd_418367 := by
    simpa [prefixWord, tailWord_418367, baseEnd_418367] using wordTrace_append hprefix tailTrace_418367
  have hstable : (prefixWord ++ tailWord_418367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418367).length < 2 ^ (prefixWord ++ tailWord_418367).sum := by decide
  have hdescent : baseEnd_418367 < baseStart_418367 := by decide
  rcases family_descends (prefixWord ++ tailWord_418367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418381 : List Nat := [1, 6, 1, 1, 2, 1, 1, 3, 2, 2, 3]
def baseStart_418381 : Nat := 118140960795 + 418381 * 2 ^ 59
def prefixEnd_418381 : Nat := 4983230072969 + 3 ^ 40 * 418381 * 2
def baseEnd_418381 : Nat := 214830549708832816113407

theorem tailTrace_418381 : CollatzResearch.WordTrace tailWord_418381 prefixEnd_418381 214830549708832816113407 := by
  unfold tailWord_418381
  simp only [CollatzResearch.WordTrace]
  refine ⟨15259608697284565631182997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10173072464856377087455331 15259608697284565631182997)
  ·
    refine ⟨715294157685214013961703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15259608697284565631182997 715294157685214013961703)
    ·
      refine ⟨1072941236527821020942555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 715294157685214013961703 1072941236527821020942555)
      ·
        refine ⟨1609411854791731531413833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1072941236527821020942555 1609411854791731531413833)
        ·
          refine ⟨1207058891093798648560375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1609411854791731531413833 1207058891093798648560375)
          ·
            refine ⟨1810588336640697972840563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1207058891093798648560375 1810588336640697972840563)
            ·
              refine ⟨2715882504961046959260845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1810588336640697972840563 2715882504961046959260845)
              ·
                refine ⟨1018455939360392609722817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2715882504961046959260845 1018455939360392609722817)
                ·
                  refine ⟨763841954520294457292113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1018455939360392609722817 763841954520294457292113)
                  ·
                    refine ⟨572881465890220842969085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 763841954520294457292113 572881465890220842969085)
                    ·
                      refine ⟨214830549708832816113407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 572881465890220842969085 214830549708832816113407)
                      ·
                        rfl

theorem cell23_418381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_418381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418381 prefixEnd_418381 := by exact prefixLift 418381
  have htrace : WordTrace (prefixWord ++ tailWord_418381) baseStart_418381 baseEnd_418381 := by
    simpa [prefixWord, tailWord_418381, baseEnd_418381] using wordTrace_append hprefix tailTrace_418381
  have hstable : (prefixWord ++ tailWord_418381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418381).length < 2 ^ (prefixWord ++ tailWord_418381).sum := by decide
  have hdescent : baseEnd_418381 < baseStart_418381 := by decide
  rcases family_descends (prefixWord ++ tailWord_418381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418405 : List Nat := [1, 3, 1, 3, 4, 2, 2, 2, 1, 4]
def baseStart_418405 : Nat := 118140960795 + 418405 * 2 ^ 59
def prefixEnd_418405 : Nat := 4983230072969 + 3 ^ 40 * 418405 * 2
def baseEnd_418405 : Nat := 71614291081513574071099

theorem tailTrace_418405 : CollatzResearch.WordTrace tailWord_418405 prefixEnd_418405 71614291081513574071099 := by
  unfold tailWord_418405
  simp only [CollatzResearch.WordTrace]
  refine ⟨15260484049197617730056669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10173656032798411820037779 15260484049197617730056669)
  ·
    refine ⟨5722681518449106648771251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15260484049197617730056669 5722681518449106648771251)
    ·
      refine ⟨8584022277673659973156877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5722681518449106648771251 8584022277673659973156877)
      ·
        refine ⟨3219008354127622489933829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8584022277673659973156877 3219008354127622489933829)
        ·
          refine ⟨603564066398929216862593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3219008354127622489933829 603564066398929216862593)
          ·
            refine ⟨452673049799196912646945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 603564066398929216862593 452673049799196912646945)
            ·
              refine ⟨339504787349397684485209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 452673049799196912646945 339504787349397684485209)
              ·
                refine ⟨254628590512048263363907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 339504787349397684485209 254628590512048263363907)
                ·
                  refine ⟨381942885768072395045861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 254628590512048263363907 381942885768072395045861)
                  ·
                    refine ⟨71614291081513574071099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 381942885768072395045861 71614291081513574071099)
                    ·
                      rfl

theorem cell23_418405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 2, 1, 4].length) (baseStart_418405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418405 prefixEnd_418405 := by exact prefixLift 418405
  have htrace : WordTrace (prefixWord ++ tailWord_418405) baseStart_418405 baseEnd_418405 := by
    simpa [prefixWord, tailWord_418405, baseEnd_418405] using wordTrace_append hprefix tailTrace_418405
  have hstable : (prefixWord ++ tailWord_418405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418405).length < 2 ^ (prefixWord ++ tailWord_418405).sum := by decide
  have hdescent : baseEnd_418405 < baseStart_418405 := by decide
  rcases family_descends (prefixWord ++ tailWord_418405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418414 : List Nat := [4, 1, 2, 2, 2, 1, 1, 2, 3, 5]
def baseStart_418414 : Nat := 118140960795 + 418414 * 2 ^ 59
def prefixEnd_418414 : Nat := 4983230072969 + 3 ^ 40 * 418414 * 2
def baseEnd_418414 : Nat := 71615831523477062333585

theorem tailTrace_418414 : CollatzResearch.WordTrace tailWord_418414 prefixEnd_418414 71615831523477062333585 := by
  unfold tailWord_418414
  simp only [CollatzResearch.WordTrace]
  refine ⟨1907601538270626533391787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10173874870776674844756197 1907601538270626533391787)
  ·
    refine ⟨2861402307405939800087681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1907601538270626533391787 2861402307405939800087681)
    ·
      refine ⟨2146051730554454850065761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2861402307405939800087681 2146051730554454850065761)
      ·
        refine ⟨1609538797915841137549321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2146051730554454850065761 1609538797915841137549321)
        ·
          refine ⟨1207154098436880853161991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1609538797915841137549321 1207154098436880853161991)
          ·
            refine ⟨1810731147655321279742987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1207154098436880853161991 1810731147655321279742987)
            ·
              refine ⟨2716096721482981919614481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1810731147655321279742987 2716096721482981919614481)
              ·
                refine ⟨2037072541112236439710861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2716096721482981919614481 2037072541112236439710861)
                ·
                  refine ⟨763902202917088664891573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2037072541112236439710861 763902202917088664891573)
                  ·
                    refine ⟨71615831523477062333585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 763902202917088664891573 71615831523477062333585)
                    ·
                      rfl

theorem cell23_418414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_418414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418414 prefixEnd_418414 := by exact prefixLift 418414
  have htrace : WordTrace (prefixWord ++ tailWord_418414) baseStart_418414 baseEnd_418414 := by
    simpa [prefixWord, tailWord_418414, baseEnd_418414] using wordTrace_append hprefix tailTrace_418414
  have hstable : (prefixWord ++ tailWord_418414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418414).length < 2 ^ (prefixWord ++ tailWord_418414).sum := by decide
  have hdescent : baseEnd_418414 < baseStart_418414 := by decide
  rcases family_descends (prefixWord ++ tailWord_418414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418461 : List Nat := [1, 4, 2, 1, 1, 1, 5, 2, 2, 4]
def baseStart_418461 : Nat := 118140960795 + 418461 * 2 ^ 59
def prefixEnd_418461 : Nat := 4983230072969 + 3 ^ 40 * 418461 * 2
def baseEnd_418461 : Nat := 71623876053730834371013

theorem tailTrace_418461 : CollatzResearch.WordTrace tailWord_418461 prefixEnd_418461 71623876053730834371013 := by
  unfold tailWord_418461
  simp only [CollatzResearch.WordTrace]
  refine ⟨15262526536994739294095237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10175017691329826196063491 15262526536994739294095237)
  ·
    refine ⟨2861723725686513617642857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15262526536994739294095237 2861723725686513617642857)
    ·
      refine ⟨2146292794264885213232143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2861723725686513617642857 2146292794264885213232143)
      ·
        refine ⟨3219439191397327819848215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2146292794264885213232143 3219439191397327819848215)
        ·
          refine ⟨4829158787095991729772323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3219439191397327819848215 4829158787095991729772323)
          ·
            refine ⟨7243738180643987594658485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4829158787095991729772323 7243738180643987594658485)
            ·
              refine ⟨679100454435373836999233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7243738180643987594658485 679100454435373836999233)
              ·
                refine ⟨509325340826530377749425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 679100454435373836999233 509325340826530377749425)
                ·
                  refine ⟨381994005619897783312069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 509325340826530377749425 381994005619897783312069)
                  ·
                    refine ⟨71623876053730834371013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 381994005619897783312069 71623876053730834371013)
                    ·
                      rfl

theorem cell23_418461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_418461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418461 prefixEnd_418461 := by exact prefixLift 418461
  have htrace : WordTrace (prefixWord ++ tailWord_418461) baseStart_418461 baseEnd_418461 := by
    simpa [prefixWord, tailWord_418461, baseEnd_418461] using wordTrace_append hprefix tailTrace_418461
  have hstable : (prefixWord ++ tailWord_418461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418461).length < 2 ^ (prefixWord ++ tailWord_418461).sum := by decide
  have hdescent : baseEnd_418461 < baseStart_418461 := by decide
  rcases family_descends (prefixWord ++ tailWord_418461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418468 : List Nat := [2, 3, 1, 2, 2, 1, 4, 1, 3, 2, 2]
def baseStart_418468 : Nat := 118140960795 + 418468 * 2 ^ 59
def prefixEnd_418468 : Nat := 4983230072969 + 3 ^ 40 * 418468 * 2
def baseEnd_418468 : Nat := 214875222525773975725507

theorem tailTrace_418468 : CollatzResearch.WordTrace tailWord_418468 prefixEnd_418468 214875222525773975725507 := by
  unfold tailWord_418468
  simp only [CollatzResearch.WordTrace]
  refine ⟨7631390923984689744800029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10175187898646252993066705 7631390923984689744800029)
  ·
    refine ⟨2861771596494258654300011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7631390923984689744800029 2861771596494258654300011)
    ·
      refine ⟨4292657394741387981450017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2861771596494258654300011 4292657394741387981450017)
      ·
        refine ⟨3219493046056040986087513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4292657394741387981450017 3219493046056040986087513)
        ·
          refine ⟨2414619784542030739565635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3219493046056040986087513 2414619784542030739565635)
          ·
            refine ⟨3621929676813046109348453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2414619784542030739565635 3621929676813046109348453)
            ·
              refine ⟨679111814402446145502835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3621929676813046109348453 679111814402446145502835)
              ·
                refine ⟨1018667721603669218254253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 679111814402446145502835 1018667721603669218254253)
                ·
                  refine ⟨382000395601375956845345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1018667721603669218254253 382000395601375956845345)
                  ·
                    refine ⟨286500296701031967634009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 382000395601375956845345 286500296701031967634009)
                    ·
                      refine ⟨214875222525773975725507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 286500296701031967634009 214875222525773975725507)
                      ·
                        rfl

theorem cell23_418468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_418468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418468 prefixEnd_418468 := by exact prefixLift 418468
  have htrace : WordTrace (prefixWord ++ tailWord_418468) baseStart_418468 baseEnd_418468 := by
    simpa [prefixWord, tailWord_418468, baseEnd_418468] using wordTrace_append hprefix tailTrace_418468
  have hstable : (prefixWord ++ tailWord_418468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418468).length < 2 ^ (prefixWord ++ tailWord_418468).sum := by decide
  have hdescent : baseEnd_418468 < baseStart_418468 := by decide
  rcases family_descends (prefixWord ++ tailWord_418468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418478 : List Nat := [4, 1, 4, 1, 1, 3, 1, 1, 1, 6]
def baseStart_418478 : Nat := 118140960795 + 418478 * 2 ^ 59
def prefixEnd_418478 : Nat := 4983230072969 + 3 ^ 40 * 418478 * 2
def baseEnd_418478 : Nat := 71626785777439645533487

theorem tailTrace_418478 : CollatzResearch.WordTrace tailWord_418478 prefixEnd_418478 71626785777439645533487 := by
  unfold tailWord_418478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1907893322241643899683011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10175431051955434131642725 1907893322241643899683011)
  ·
    refine ⟨2861839983362465849524517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1907893322241643899683011 2861839983362465849524517)
    ·
      refine ⟨536594996880462346785847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2861839983362465849524517 536594996880462346785847)
      ·
        refine ⟨804892495320693520178771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 536594996880462346785847 804892495320693520178771)
        ·
          refine ⟨1207338742981040280268157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 804892495320693520178771 1207338742981040280268157)
          ·
            refine ⟨452752028617890105100559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1207338742981040280268157 452752028617890105100559)
            ·
              refine ⟨679128042926835157650839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 452752028617890105100559 679128042926835157650839)
              ·
                refine ⟨1018692064390252736476259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 679128042926835157650839 1018692064390252736476259)
                ·
                  refine ⟨1528038096585379104714389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1018692064390252736476259 1528038096585379104714389)
                  ·
                    refine ⟨71626785777439645533487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1528038096585379104714389 71626785777439645533487)
                    ·
                      rfl

theorem cell23_418478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_418478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418478 prefixEnd_418478 := by exact prefixLift 418478
  have htrace : WordTrace (prefixWord ++ tailWord_418478) baseStart_418478 baseEnd_418478 := by
    simpa [prefixWord, tailWord_418478, baseEnd_418478] using wordTrace_append hprefix tailTrace_418478
  have hstable : (prefixWord ++ tailWord_418478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418478).length < 2 ^ (prefixWord ++ tailWord_418478).sum := by decide
  have hdescent : baseEnd_418478 < baseStart_418478 := by decide
  rcases family_descends (prefixWord ++ tailWord_418478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418481 : List Nat := [1, 2, 2, 6, 1, 1, 1, 1, 1, 1, 6]
def baseStart_418481 : Nat := 118140960795 + 418481 * 2 ^ 59
def prefixEnd_418481 : Nat := 4983230072969 + 3 ^ 40 * 418481 * 2
def baseEnd_418481 : Nat := 214881897774282424862947

theorem tailTrace_418481 : CollatzResearch.WordTrace tailWord_418481 prefixEnd_418481 214881897774282424862947 := by
  unfold tailWord_418481
  simp only [CollatzResearch.WordTrace]
  refine ⟨15263255996922282709823297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10175503997948188473215531 15263255996922282709823297)
  ·
    refine ⟨11447441997691712032367473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15263255996922282709823297 11447441997691712032367473)
    ·
      refine ⟨8585581498268784024275605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11447441997691712032367473 8585581498268784024275605)
      ·
        refine ⟨402449132731349251137919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8585581498268784024275605 402449132731349251137919)
        ·
          refine ⟨603673699097023876706879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402449132731349251137919 603673699097023876706879)
          ·
            refine ⟨905510548645535815060319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 603673699097023876706879 905510548645535815060319)
            ·
              refine ⟨1358265822968303722590479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 905510548645535815060319 1358265822968303722590479)
              ·
                refine ⟨2037398734452455583885719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1358265822968303722590479 2037398734452455583885719)
                ·
                  refine ⟨3056098101678683375828579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2037398734452455583885719 3056098101678683375828579)
                  ·
                    refine ⟨4584147152518025063742869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3056098101678683375828579 4584147152518025063742869)
                    ·
                      refine ⟨214881897774282424862947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4584147152518025063742869 214881897774282424862947)
                      ·
                        rfl

theorem cell23_418481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_418481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418481 prefixEnd_418481 := by exact prefixLift 418481
  have htrace : WordTrace (prefixWord ++ tailWord_418481) baseStart_418481 baseEnd_418481 := by
    simpa [prefixWord, tailWord_418481, baseEnd_418481] using wordTrace_append hprefix tailTrace_418481
  have hstable : (prefixWord ++ tailWord_418481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418481).length < 2 ^ (prefixWord ++ tailWord_418481).sum := by decide
  have hdescent : baseEnd_418481 < baseStart_418481 := by decide
  rcases family_descends (prefixWord ++ tailWord_418481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418507 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 4]
def baseStart_418507 : Nat := 118140960795 + 418507 * 2 ^ 59
def prefixEnd_418507 : Nat := 4983230072969 + 3 ^ 40 * 418507 * 2
def baseEnd_418507 : Nat := 214895248271299323137827

theorem tailTrace_418507 : CollatzResearch.WordTrace tailWord_418507 prefixEnd_418507 214895248271299323137827 := by
  unfold tailWord_418507
  simp only [CollatzResearch.WordTrace]
  refine ⟨15264204294828089150269775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10176136196552059433513183 15264204294828089150269775)
  ·
    refine ⟨22896306442242133725404663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15264204294828089150269775 22896306442242133725404663)
    ·
      refine ⟨34344459663363200588106995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22896306442242133725404663 34344459663363200588106995)
      ·
        refine ⟨51516689495044800882160493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34344459663363200588106995 51516689495044800882160493)
        ·
          refine ⟨19318758560641800330810185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51516689495044800882160493 19318758560641800330810185)
          ·
            refine ⟨14489068920481350248107639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19318758560641800330810185 14489068920481350248107639)
            ·
              refine ⟨21733603380722025372161459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14489068920481350248107639 21733603380722025372161459)
              ·
                refine ⟨32600405071083038058242189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21733603380722025372161459 32600405071083038058242189)
                ·
                  refine ⟨12225151901656139271840821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32600405071083038058242189 12225151901656139271840821)
                  ·
                    refine ⟨1146107990780263056735077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12225151901656139271840821 1146107990780263056735077)
                    ·
                      refine ⟨214895248271299323137827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1146107990780263056735077 214895248271299323137827)
                      ·
                        rfl

theorem cell23_418507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 4].length) (baseStart_418507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418507 prefixEnd_418507 := by exact prefixLift 418507
  have htrace : WordTrace (prefixWord ++ tailWord_418507) baseStart_418507 baseEnd_418507 := by
    simpa [prefixWord, tailWord_418507, baseEnd_418507] using wordTrace_append hprefix tailTrace_418507
  have hstable : (prefixWord ++ tailWord_418507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418507).length < 2 ^ (prefixWord ++ tailWord_418507).sum := by decide
  have hdescent : baseEnd_418507 < baseStart_418507 := by decide
  rcases family_descends (prefixWord ++ tailWord_418507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418547 : List Nat := [1, 1, 1, 2, 2, 3, 1, 3, 9]
def baseStart_418547 : Nat := 118140960795 + 418547 * 2 ^ 59
def prefixEnd_418547 : Nat := 4983230072969 + 3 ^ 40 * 418547 * 2
def baseEnd_418547 : Nat := 23879531944164351848627

theorem tailTrace_418547 : CollatzResearch.WordTrace tailWord_418547 prefixEnd_418547 23879531944164351848627 := by
  unfold tailWord_418547
  simp only [CollatzResearch.WordTrace]
  refine ⟨15265663214683175981725895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10177108809788783987817263 15265663214683175981725895)
  ·
    refine ⟨22898494822024763972588843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15265663214683175981725895 22898494822024763972588843)
    ·
      refine ⟨34347742233037145958883265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22898494822024763972588843 34347742233037145958883265)
      ·
        refine ⟨25760806674777859469162449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34347742233037145958883265 25760806674777859469162449)
        ·
          refine ⟨19320605006083394601871837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25760806674777859469162449 19320605006083394601871837)
          ·
            refine ⟨7245226877281272975701939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19320605006083394601871837 7245226877281272975701939)
            ·
              refine ⟨10867840315921909463552909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7245226877281272975701939 10867840315921909463552909)
              ·
                refine ⟨4075440118470716048832341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10867840315921909463552909 4075440118470716048832341)
                ·
                  refine ⟨23879531944164351848627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4075440118470716048832341 23879531944164351848627)
                  ·
                    rfl

theorem cell23_418547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 9].length) (baseStart_418547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418547 prefixEnd_418547 := by exact prefixLift 418547
  have htrace : WordTrace (prefixWord ++ tailWord_418547) baseStart_418547 baseEnd_418547 := by
    simpa [prefixWord, tailWord_418547, baseEnd_418547] using wordTrace_append hprefix tailTrace_418547
  have hstable : (prefixWord ++ tailWord_418547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418547).length < 2 ^ (prefixWord ++ tailWord_418547).sum := by decide
  have hdescent : baseEnd_418547 < baseStart_418547 := by decide
  rcases family_descends (prefixWord ++ tailWord_418547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418558 : List Nat := [4, 2, 2, 1, 2, 1, 1, 1, 3, 4, 2]
def baseStart_418558 : Nat := 118140960795 + 418558 * 2 ^ 59
def prefixEnd_418558 : Nat := 4983230072969 + 3 ^ 40 * 418558 * 2
def baseEnd_418558 : Nat := 214921435784678623600093

theorem tailTrace_418558 : CollatzResearch.WordTrace tailWord_418558 prefixEnd_418558 214921435784678623600093 := by
  unfold tailWord_418558
  simp only [CollatzResearch.WordTrace]
  refine ⟨1908258052205415607547041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10177376278428883240250885 1908258052205415607547041)
  ·
    refine ⟨1431193539154061705660281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1908258052205415607547041 1431193539154061705660281)
    ·
      refine ⟨1073395154365546279245211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1431193539154061705660281 1073395154365546279245211)
      ·
        refine ⟨1610092731548319418867817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1073395154365546279245211 1610092731548319418867817)
        ·
          refine ⟨1207569548661239564150863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1610092731548319418867817 1207569548661239564150863)
          ·
            refine ⟨1811354322991859346226295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1207569548661239564150863 1811354322991859346226295)
            ·
              refine ⟨2717031484487789019339443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1811354322991859346226295 2717031484487789019339443)
              ·
                refine ⟨4075547226731683529009165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2717031484487789019339443 4075547226731683529009165)
                ·
                  refine ⟨1528330210024381323378437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4075547226731683529009165 1528330210024381323378437)
                  ·
                    refine ⟨286561914379571498133457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1528330210024381323378437 286561914379571498133457)
                    ·
                      refine ⟨214921435784678623600093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 286561914379571498133457 214921435784678623600093)
                      ·
                        rfl

theorem cell23_418558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_418558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418558 prefixEnd_418558 := by exact prefixLift 418558
  have htrace : WordTrace (prefixWord ++ tailWord_418558) baseStart_418558 baseEnd_418558 := by
    simpa [prefixWord, tailWord_418558, baseEnd_418558] using wordTrace_append hprefix tailTrace_418558
  have hstable : (prefixWord ++ tailWord_418558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418558).length < 2 ^ (prefixWord ++ tailWord_418558).sum := by decide
  have hdescent : baseEnd_418558 < baseStart_418558 := by decide
  rcases family_descends (prefixWord ++ tailWord_418558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418562 : List Nat := [3, 4, 1, 1, 1, 3, 3, 1, 1, 3, 2]
def baseStart_418562 : Nat := 118140960795 + 418562 * 2 ^ 59
def prefixEnd_418562 : Nat := 4983230072969 + 3 ^ 40 * 418562 * 2
def baseEnd_418562 : Nat := 214923489707296607950075

theorem tailTrace_418562 : CollatzResearch.WordTrace tailWord_418562 prefixEnd_418562 214923489707296607950075 := by
  unfold tailWord_418562
  simp only [CollatzResearch.WordTrace]
  refine ⟨3816552577407208385880485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10177473539752555695681293 3816552577407208385880485)
  ·
    refine ⟨715603608263851572352591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3816552577407208385880485 715603608263851572352591)
    ·
      refine ⟨1073405412395777358528887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 715603608263851572352591 1073405412395777358528887)
      ·
        refine ⟨1610108118593666037793331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1073405412395777358528887 1610108118593666037793331)
        ·
          refine ⟨2415162177890499056689997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1610108118593666037793331 2415162177890499056689997)
          ·
            refine ⟨905685816708937146258749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2415162177890499056689997 905685816708937146258749)
            ·
              refine ⟨339632181265851429847031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 905685816708937146258749 339632181265851429847031)
              ·
                refine ⟨509448271898777144770547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 339632181265851429847031 509448271898777144770547)
                ·
                  refine ⟨764172407848165717155821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 509448271898777144770547 764172407848165717155821)
                  ·
                    refine ⟨286564652943062143933433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 764172407848165717155821 286564652943062143933433)
                    ·
                      refine ⟨214923489707296607950075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 286564652943062143933433 214923489707296607950075)
                      ·
                        rfl

theorem cell23_418562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_418562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418562 prefixEnd_418562 := by exact prefixLift 418562
  have htrace : WordTrace (prefixWord ++ tailWord_418562) baseStart_418562 baseEnd_418562 := by
    simpa [prefixWord, tailWord_418562, baseEnd_418562] using wordTrace_append hprefix tailTrace_418562
  have hstable : (prefixWord ++ tailWord_418562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418562).length < 2 ^ (prefixWord ++ tailWord_418562).sum := by decide
  have hdescent : baseEnd_418562 < baseStart_418562 := by decide
  rcases family_descends (prefixWord ++ tailWord_418562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418581 : List Nat := [1, 3, 2, 1, 2, 2, 3, 4, 5]
def baseStart_418581 : Nat := 118140960795 + 418581 * 2 ^ 59
def prefixEnd_418581 : Nat := 4983230072969 + 3 ^ 40 * 418581 * 2
def baseEnd_418581 : Nat := 23881471759970225956943

theorem tailTrace_418581 : CollatzResearch.WordTrace tailWord_418581 prefixEnd_418581 23881471759970225956943 := by
  unfold tailWord_418581
  simp only [CollatzResearch.WordTrace]
  refine ⟨15266903296559999788463597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10177935531039999858975731 15266903296559999788463597)
  ·
    refine ⟨5725088736209999920673849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15266903296559999788463597 5725088736209999920673849)
    ·
      refine ⟨4293816552157499940505387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5725088736209999920673849 4293816552157499940505387)
      ·
        refine ⟨6440724828236249910758081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4293816552157499940505387 6440724828236249910758081)
        ·
          refine ⟨4830543621177187433068561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6440724828236249910758081 4830543621177187433068561)
          ·
            refine ⟨3622907715882890574801421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4830543621177187433068561 3622907715882890574801421)
            ·
              refine ⟨1358590393456083965550533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3622907715882890574801421 1358590393456083965550533)
              ·
                refine ⟨254735698773015743540725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1358590393456083965550533 254735698773015743540725)
                ·
                  refine ⟨23881471759970225956943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 254735698773015743540725 23881471759970225956943)
                  ·
                    rfl

theorem cell23_418581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 4, 5].length) (baseStart_418581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418581 prefixEnd_418581 := by exact prefixLift 418581
  have htrace : WordTrace (prefixWord ++ tailWord_418581) baseStart_418581 baseEnd_418581 := by
    simpa [prefixWord, tailWord_418581, baseEnd_418581] using wordTrace_append hprefix tailTrace_418581
  have hstable : (prefixWord ++ tailWord_418581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418581).length < 2 ^ (prefixWord ++ tailWord_418581).sum := by decide
  have hdescent : baseEnd_418581 < baseStart_418581 := by decide
  rcases family_descends (prefixWord ++ tailWord_418581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418591 : List Nat := [1, 1, 2, 4, 2, 3, 1, 1, 2, 3, 3]
def baseStart_418591 : Nat := 118140960795 + 418591 * 2 ^ 59
def prefixEnd_418591 : Nat := 4983230072969 + 3 ^ 40 * 418591 * 2
def baseEnd_418591 : Nat := 214938380646276994487441

theorem tailTrace_418591 : CollatzResearch.WordTrace tailWord_418591 prefixEnd_418591 214938380646276994487441 := by
  unfold tailWord_418591
  simp only [CollatzResearch.WordTrace]
  refine ⟨15267268026523771496327627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10178178684349180997551751 15267268026523771496327627)
  ·
    refine ⟨22900902039785657244491441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15267268026523771496327627 22900902039785657244491441)
    ·
      refine ⟨17175676529839242933368581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22900902039785657244491441 17175676529839242933368581)
      ·
        refine ⟨3220439349344858050006609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17175676529839242933368581 3220439349344858050006609)
        ·
          refine ⟨2415329512008643537504957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3220439349344858050006609 2415329512008643537504957)
          ·
            refine ⟨905748567003241326564359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2415329512008643537504957 905748567003241326564359)
            ·
              refine ⟨1358622850504861989846539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 905748567003241326564359 1358622850504861989846539)
              ·
                refine ⟨2037934275757292984769809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1358622850504861989846539 2037934275757292984769809)
                ·
                  refine ⟨1528450706817969738577357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2037934275757292984769809 1528450706817969738577357)
                  ·
                    refine ⟨573169015056738651966509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1528450706817969738577357 573169015056738651966509)
                    ·
                      refine ⟨214938380646276994487441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 573169015056738651966509 214938380646276994487441)
                      ·
                        rfl

theorem cell23_418591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_418591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418591 prefixEnd_418591 := by exact prefixLift 418591
  have htrace : WordTrace (prefixWord ++ tailWord_418591) baseStart_418591 baseEnd_418591 := by
    simpa [prefixWord, tailWord_418591, baseEnd_418591] using wordTrace_append hprefix tailTrace_418591
  have hstable : (prefixWord ++ tailWord_418591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418591).length < 2 ^ (prefixWord ++ tailWord_418591).sum := by decide
  have hdescent : baseEnd_418591 < baseStart_418591 := by decide
  rcases family_descends (prefixWord ++ tailWord_418591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418611 : List Nat := [1, 1, 1, 2, 6, 1, 3, 1, 2, 5]
def baseStart_418611 : Nat := 118140960795 + 418611 * 2 ^ 59
def prefixEnd_418611 : Nat := 4983230072969 + 3 ^ 40 * 418611 * 2
def baseEnd_418611 : Nat := 71649550086455638745783

theorem tailTrace_418611 : CollatzResearch.WordTrace tailWord_418611 prefixEnd_418611 71649550086455638745783 := by
  unfold tailWord_418611
  simp only [CollatzResearch.WordTrace]
  refine ⟨15267997486451314912055687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10178664990967543274703791 15267997486451314912055687)
  ·
    refine ⟨22901996229676972368083531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15267997486451314912055687 22901996229676972368083531)
    ·
      refine ⟨34352994344515458552125297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22901996229676972368083531 34352994344515458552125297)
      ·
        refine ⟨25764745758386593914093973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34352994344515458552125297 25764745758386593914093973)
        ·
          refine ⟨1207722457424371589723155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25764745758386593914093973 1207722457424371589723155)
          ·
            refine ⟨1811583686136557384584733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1207722457424371589723155 1811583686136557384584733)
            ·
              refine ⟨679343882301209019219275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1811583686136557384584733 679343882301209019219275)
              ·
                refine ⟨1019015823451813528828913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 679343882301209019219275 1019015823451813528828913)
                ·
                  refine ⟨764261867588860146621685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1019015823451813528828913 764261867588860146621685)
                  ·
                    refine ⟨71649550086455638745783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 764261867588860146621685 71649550086455638745783)
                    ·
                      rfl

theorem cell23_418611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 5].length) (baseStart_418611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418611 prefixEnd_418611 := by exact prefixLift 418611
  have htrace : WordTrace (prefixWord ++ tailWord_418611) baseStart_418611 baseEnd_418611 := by
    simpa [prefixWord, tailWord_418611, baseEnd_418611] using wordTrace_append hprefix tailTrace_418611
  have hstable : (prefixWord ++ tailWord_418611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418611).length < 2 ^ (prefixWord ++ tailWord_418611).sum := by decide
  have hdescent : baseEnd_418611 < baseStart_418611 := by decide
  rcases family_descends (prefixWord ++ tailWord_418611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418744 : List Nat := [2, 1, 2, 1, 2, 15]
def baseStart_418744 : Nat := 118140960795 + 418744 * 2 ^ 59
def prefixEnd_418744 : Nat := 4983230072969 + 3 ^ 40 * 418744 * 2
def baseEnd_418744 : Nat := 884843387598415209359

theorem tailTrace_418744 : CollatzResearch.WordTrace tailWord_418744 prefixEnd_418744 884843387598415209359 := by
  unfold tailWord_418744
  simp only [CollatzResearch.WordTrace]
  refine ⟨7636424197484739313323643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10181898929979652417764857 7636424197484739313323643)
  ·
    refine ⟨11454636296227108969985465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7636424197484739313323643 11454636296227108969985465)
    ·
      refine ⟨8590977222170331727489099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11454636296227108969985465 8590977222170331727489099)
      ·
        refine ⟨12886465833255497591233649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8590977222170331727489099 12886465833255497591233649)
        ·
          refine ⟨9664849374941623193425237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12886465833255497591233649 9664849374941623193425237)
          ·
            refine ⟨884843387598415209359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 9664849374941623193425237 884843387598415209359)
            ·
              rfl

theorem cell23_418744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 15].length) (baseStart_418744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418744 prefixEnd_418744 := by exact prefixLift 418744
  have htrace : WordTrace (prefixWord ++ tailWord_418744) baseStart_418744 baseEnd_418744 := by
    simpa [prefixWord, tailWord_418744, baseEnd_418744] using wordTrace_append hprefix tailTrace_418744
  have hstable : (prefixWord ++ tailWord_418744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418744).length < 2 ^ (prefixWord ++ tailWord_418744).sum := by decide
  have hdescent : baseEnd_418744 < baseStart_418744 := by decide
  rcases family_descends (prefixWord ++ tailWord_418744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418772 : List Nat := [2, 4, 1, 2, 1, 3, 1, 2, 3, 2, 2]
def baseStart_418772 : Nat := 118140960795 + 418772 * 2 ^ 59
def prefixEnd_418772 : Nat := 4983230072969 + 3 ^ 40 * 418772 * 2
def baseEnd_418772 : Nat := 215031320644740786324109

theorem tailTrace_418772 : CollatzResearch.WordTrace tailWord_418772 prefixEnd_418772 215031320644740786324109 := by
  unfold tailWord_418772
  simp only [CollatzResearch.WordTrace]
  refine ⟨7636934819434019704333285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10182579759245359605777713 7636934819434019704333285)
  ·
    refine ⟨1431925278643878694562491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7636934819434019704333285 1431925278643878694562491)
    ·
      refine ⟨2147887917965818041843737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1431925278643878694562491 2147887917965818041843737)
      ·
        refine ⟨1610915938474363531382803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2147887917965818041843737 1610915938474363531382803)
        ·
          refine ⟨2416373907711545297074205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1610915938474363531382803 2416373907711545297074205)
          ·
            refine ⟨906140215391829486402827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2416373907711545297074205 906140215391829486402827)
            ·
              refine ⟨1359210323087744229604241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 906140215391829486402827 1359210323087744229604241)
              ·
                refine ⟨1019407742315808172203181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1359210323087744229604241 1019407742315808172203181)
                ·
                  refine ⟨382277903368428064576193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1019407742315808172203181 382277903368428064576193)
                  ·
                    refine ⟨286708427526321048432145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 382277903368428064576193 286708427526321048432145)
                    ·
                      refine ⟨215031320644740786324109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 286708427526321048432145 215031320644740786324109)
                      ·
                        rfl

theorem cell23_418772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_418772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418772 prefixEnd_418772 := by exact prefixLift 418772
  have htrace : WordTrace (prefixWord ++ tailWord_418772) baseStart_418772 baseEnd_418772 := by
    simpa [prefixWord, tailWord_418772, baseEnd_418772] using wordTrace_append hprefix tailTrace_418772
  have hstable : (prefixWord ++ tailWord_418772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418772).length < 2 ^ (prefixWord ++ tailWord_418772).sum := by decide
  have hdescent : baseEnd_418772 < baseStart_418772 := by decide
  rcases family_descends (prefixWord ++ tailWord_418772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418778 : List Nat := [3, 1, 1, 2, 4, 2, 3, 7]
def baseStart_418778 : Nat := 118140960795 + 418778 * 2 ^ 59
def prefixEnd_418778 : Nat := 4983230072969 + 3 ^ 40 * 418778 * 2
def baseEnd_418778 : Nat := 7964237093654361587003

theorem tailTrace_418778 : CollatzResearch.WordTrace tailWord_418778 prefixEnd_418778 7964237093654361587003 := by
  unfold tailWord_418778
  simp only [CollatzResearch.WordTrace]
  refine ⟨3818522119211575608346247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10182725651230868288923325 3818522119211575608346247)
  ·
    refine ⟨5727783178817363412519371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3818522119211575608346247 5727783178817363412519371)
    ·
      refine ⟨8591674768226045118779057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5727783178817363412519371 8591674768226045118779057)
      ·
        refine ⟨6443756076169533839084293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8591674768226045118779057 6443756076169533839084293)
        ·
          refine ⟨1208204264281787594828305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6443756076169533839084293 1208204264281787594828305)
          ·
            refine ⟨906153198211340696121229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1208204264281787594828305 906153198211340696121229)
            ·
              refine ⟨339807449329252761045461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 906153198211340696121229 339807449329252761045461)
              ·
                refine ⟨7964237093654361587003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 339807449329252761045461 7964237093654361587003)
                ·
                  rfl

theorem cell23_418778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 7].length) (baseStart_418778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418778 prefixEnd_418778 := by exact prefixLift 418778
  have htrace : WordTrace (prefixWord ++ tailWord_418778) baseStart_418778 baseEnd_418778 := by
    simpa [prefixWord, tailWord_418778, baseEnd_418778] using wordTrace_append hprefix tailTrace_418778
  have hstable : (prefixWord ++ tailWord_418778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418778).length < 2 ^ (prefixWord ++ tailWord_418778).sum := by decide
  have hdescent : baseEnd_418778 < baseStart_418778 := by decide
  rcases family_descends (prefixWord ++ tailWord_418778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418789 : List Nat := [1, 3, 1, 6, 1, 2, 2, 1, 1, 1, 4]
def baseStart_418789 : Nat := 118140960795 + 418789 * 2 ^ 59
def prefixEnd_418789 : Nat := 4983230072969 + 3 ^ 40 * 418789 * 2
def baseEnd_418789 : Nat := 215040049815867219811531

theorem tailTrace_418789 : CollatzResearch.WordTrace tailWord_418789 prefixEnd_418789 215040049815867219811531 := by
  unfold tailWord_418789
  simp only [CollatzResearch.WordTrace]
  refine ⟨15274489679806451312035421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10182993119870967541356947 15274489679806451312035421)
  ·
    refine ⟨5727933629927419242013283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15274489679806451312035421 5727933629927419242013283)
    ·
      refine ⟨8591900444891128863019925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5727933629927419242013283 8591900444891128863019925)
      ·
        refine ⟨402745333354271665454059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8591900444891128863019925 402745333354271665454059)
        ·
          refine ⟨604118000031407498181089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402745333354271665454059 604118000031407498181089)
          ·
            refine ⟨453088500023555623635817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 604118000031407498181089 453088500023555623635817)
            ·
              refine ⟨339816375017666717726863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 453088500023555623635817 339816375017666717726863)
              ·
                refine ⟨509724562526500076590295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 339816375017666717726863 509724562526500076590295)
                ·
                  refine ⟨764586843789750114885443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 509724562526500076590295 764586843789750114885443)
                  ·
                    refine ⟨1146880265684625172328165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 764586843789750114885443 1146880265684625172328165)
                    ·
                      refine ⟨215040049815867219811531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1146880265684625172328165 215040049815867219811531)
                      ·
                        rfl

theorem cell23_418789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_418789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418789 prefixEnd_418789 := by exact prefixLift 418789
  have htrace : WordTrace (prefixWord ++ tailWord_418789) baseStart_418789 baseEnd_418789 := by
    simpa [prefixWord, tailWord_418789, baseEnd_418789] using wordTrace_append hprefix tailTrace_418789
  have hstable : (prefixWord ++ tailWord_418789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418789).length < 2 ^ (prefixWord ++ tailWord_418789).sum := by decide
  have hdescent : baseEnd_418789 < baseStart_418789 := by decide
  rcases family_descends (prefixWord ++ tailWord_418789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418821 : List Nat := [1, 3, 1, 1, 2, 3, 1, 3, 2, 6]
def baseStart_418821 : Nat := 118140960795 + 418821 * 2 ^ 59
def prefixEnd_418821 : Nat := 4983230072969 + 3 ^ 40 * 418821 * 2
def baseEnd_418821 : Nat := 71685493732270364870461

theorem tailTrace_418821 : CollatzResearch.WordTrace tailWord_418821 prefixEnd_418821 71685493732270364870461 := by
  unfold tailWord_418821
  simp only [CollatzResearch.WordTrace]
  refine ⟨15275656815690520777200317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10183771210460347184800211 15275656815690520777200317)
  ·
    refine ⟨5728371305883945291450119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15275656815690520777200317 5728371305883945291450119)
    ·
      refine ⟨8592556958825917937175179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5728371305883945291450119 8592556958825917937175179)
      ·
        refine ⟨12888835438238876905762769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8592556958825917937175179 12888835438238876905762769)
        ·
          refine ⟨9666626578679157679322077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12888835438238876905762769 9666626578679157679322077)
          ·
            refine ⟨3624984967004684129745779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9666626578679157679322077 3624984967004684129745779)
            ·
              refine ⟨5437477450507026194618669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3624984967004684129745779 5437477450507026194618669)
              ·
                refine ⟨2039054043940134822982001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5437477450507026194618669 2039054043940134822982001)
                ·
                  refine ⟨1529290532955101117236501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2039054043940134822982001 1529290532955101117236501)
                  ·
                    refine ⟨71685493732270364870461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1529290532955101117236501 71685493732270364870461)
                    ·
                      rfl

theorem cell23_418821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 2, 6].length) (baseStart_418821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418821 prefixEnd_418821 := by exact prefixLift 418821
  have htrace : WordTrace (prefixWord ++ tailWord_418821) baseStart_418821 baseEnd_418821 := by
    simpa [prefixWord, tailWord_418821, baseEnd_418821] using wordTrace_append hprefix tailTrace_418821
  have hstable : (prefixWord ++ tailWord_418821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418821).length < 2 ^ (prefixWord ++ tailWord_418821).sum := by decide
  have hdescent : baseEnd_418821 < baseStart_418821 := by decide
  rcases family_descends (prefixWord ++ tailWord_418821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418841 : List Nat := [1, 2, 1, 2, 1, 1, 4, 2, 1, 4, 4]
def baseStart_418841 : Nat := 118140960795 + 418841 * 2 ^ 59
def prefixEnd_418841 : Nat := 4983230072969 + 3 ^ 40 * 418841 * 2
def baseEnd_418841 : Nat := 215066750809901016361291

theorem tailTrace_418841 : CollatzResearch.WordTrace tailWord_418841 prefixEnd_418841 215066750809901016361291 := by
  unfold tailWord_418841
  simp only [CollatzResearch.WordTrace]
  refine ⟨15276386275618064192928377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10184257517078709461952251 15276386275618064192928377)
  ·
    refine ⟨11457289706713548144696283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15276386275618064192928377 11457289706713548144696283)
    ·
      refine ⟨17185934560070322217044425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11457289706713548144696283 17185934560070322217044425)
      ·
        refine ⟨12889450920052741662783319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17185934560070322217044425 12889450920052741662783319)
        ·
          refine ⟨19334176380079112494174979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12889450920052741662783319 19334176380079112494174979)
          ·
            refine ⟨29001264570118668741262469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19334176380079112494174979 29001264570118668741262469)
            ·
              refine ⟨5437737106897250388986713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29001264570118668741262469 5437737106897250388986713)
              ·
                refine ⟨4078302830172937791740035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5437737106897250388986713 4078302830172937791740035)
                ·
                  refine ⟨6117454245259406687610053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4078302830172937791740035 6117454245259406687610053)
                  ·
                    refine ⟨1147022670986138753926885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6117454245259406687610053 1147022670986138753926885)
                    ·
                      refine ⟨215066750809901016361291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1147022670986138753926885 215066750809901016361291)
                      ·
                        rfl

theorem cell23_418841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 4, 4].length) (baseStart_418841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418841 prefixEnd_418841 := by exact prefixLift 418841
  have htrace : WordTrace (prefixWord ++ tailWord_418841) baseStart_418841 baseEnd_418841 := by
    simpa [prefixWord, tailWord_418841, baseEnd_418841] using wordTrace_append hprefix tailTrace_418841
  have hstable : (prefixWord ++ tailWord_418841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418841).length < 2 ^ (prefixWord ++ tailWord_418841).sum := by decide
  have hdescent : baseEnd_418841 < baseStart_418841 := by decide
  rcases family_descends (prefixWord ++ tailWord_418841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418862 : List Nat := [4, 1, 3, 1, 1, 1, 1, 3, 4, 2, 2]
def baseStart_418862 : Nat := 118140960795 + 418862 * 2 ^ 59
def prefixEnd_418862 : Nat := 4983230072969 + 3 ^ 40 * 418862 * 2
def baseEnd_418862 : Nat := 215077533903645434198695

theorem tailTrace_418862 : CollatzResearch.WordTrace tailWord_418862 prefixEnd_418862 215077533903645434198695 := by
  unfold tailWord_418862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1909644026067748097430355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10184768139027989852961893 1909644026067748097430355)
  ·
    refine ⟨2864466039101622146145533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1909644026067748097430355 2864466039101622146145533)
    ·
      refine ⟨1074174764663108304804575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2864466039101622146145533 1074174764663108304804575)
      ·
        refine ⟨1611262146994662457206863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1074174764663108304804575 1611262146994662457206863)
        ·
          refine ⟨2416893220491993685810295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1611262146994662457206863 2416893220491993685810295)
          ·
            refine ⟨3625339830737990528715443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2416893220491993685810295 3625339830737990528715443)
            ·
              refine ⟨5438009746106985793073165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3625339830737990528715443 5438009746106985793073165)
              ·
                refine ⟨2039253654790119672402437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5438009746106985793073165 2039253654790119672402437)
                ·
                  refine ⟨382360060273147438575457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2039253654790119672402437 382360060273147438575457)
                  ·
                    refine ⟨286770045204860578931593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 382360060273147438575457 286770045204860578931593)
                    ·
                      refine ⟨215077533903645434198695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 286770045204860578931593 215077533903645434198695)
                      ·
                        rfl

theorem cell23_418862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_418862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418862 prefixEnd_418862 := by exact prefixLift 418862
  have htrace : WordTrace (prefixWord ++ tailWord_418862) baseStart_418862 baseEnd_418862 := by
    simpa [prefixWord, tailWord_418862, baseEnd_418862] using wordTrace_append hprefix tailTrace_418862
  have hstable : (prefixWord ++ tailWord_418862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418862).length < 2 ^ (prefixWord ++ tailWord_418862).sum := by decide
  have hdescent : baseEnd_418862 < baseStart_418862 := by decide
  rcases family_descends (prefixWord ++ tailWord_418862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418891 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 5]
def baseStart_418891 : Nat := 118140960795 + 418891 * 2 ^ 59
def prefixEnd_418891 : Nat := 4983230072969 + 3 ^ 40 * 418891 * 2
def baseEnd_418891 : Nat := 215092424842625820736061

theorem tailTrace_418891 : CollatzResearch.WordTrace tailWord_418891 prefixEnd_418891 215092424842625820736061 := by
  unfold tailWord_418891
  simp only [CollatzResearch.WordTrace]
  refine ⟨15278209925436922732248527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10185473283624615154832351 15278209925436922732248527)
  ·
    refine ⟨22917314888155384098372791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15278209925436922732248527 22917314888155384098372791)
    ·
      refine ⟨34375972332233076147559187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22917314888155384098372791 34375972332233076147559187)
      ·
        refine ⟨51563958498349614221338781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34375972332233076147559187 51563958498349614221338781)
        ·
          refine ⟨19336484436881105333002043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51563958498349614221338781 19336484436881105333002043)
          ·
            refine ⟨29004726655321657999503065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19336484436881105333002043 29004726655321657999503065)
            ·
              refine ⟨21753544991491243499627299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29004726655321657999503065 21753544991491243499627299)
              ·
                refine ⟨32630317487236865249440949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21753544991491243499627299 32630317487236865249440949)
                ·
                  refine ⟨3059092264428456117135089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32630317487236865249440949 3059092264428456117135089)
                  ·
                    refine ⟨2294319198321342087851317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3059092264428456117135089 2294319198321342087851317)
                    ·
                      refine ⟨215092424842625820736061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2294319198321342087851317 215092424842625820736061)
                      ·
                        rfl

theorem cell23_418891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 5].length) (baseStart_418891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418891 prefixEnd_418891 := by exact prefixLift 418891
  have htrace : WordTrace (prefixWord ++ tailWord_418891) baseStart_418891 baseEnd_418891 := by
    simpa [prefixWord, tailWord_418891, baseEnd_418891] using wordTrace_append hprefix tailTrace_418891
  have hstable : (prefixWord ++ tailWord_418891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418891).length < 2 ^ (prefixWord ++ tailWord_418891).sum := by decide
  have hdescent : baseEnd_418891 < baseStart_418891 := by decide
  rcases family_descends (prefixWord ++ tailWord_418891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418908 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 3, 2, 5]
def baseStart_418908 : Nat := 118140960795 + 418908 * 2 ^ 59
def prefixEnd_418908 : Nat := 4983230072969 + 3 ^ 40 * 418908 * 2
def baseEnd_418908 : Nat := 215101154013752254223483

theorem tailTrace_418908 : CollatzResearch.WordTrace tailWord_418908 prefixEnd_418908 215101154013752254223483 := by
  unfold tailWord_418908
  simp only [CollatzResearch.WordTrace]
  refine ⟨7639414983187667317808689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10185886644250223090411585 7639414983187667317808689)
  ·
    refine ⟨5729561237390750488356517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7639414983187667317808689 5729561237390750488356517)
    ·
      refine ⟨1074292732010765716566847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5729561237390750488356517 1074292732010765716566847)
      ·
        refine ⟨1611439098016148574850271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1074292732010765716566847 1611439098016148574850271)
        ·
          refine ⟨2417158647024222862275407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1611439098016148574850271 2417158647024222862275407)
          ·
            refine ⟨3625737970536334293413111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2417158647024222862275407 3625737970536334293413111)
            ·
              refine ⟨5438606955804501440119667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3625737970536334293413111 5438606955804501440119667)
              ·
                refine ⟨8157910433706752160179501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5438606955804501440119667 8157910433706752160179501)
                ·
                  refine ⟨3059216412640032060067313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8157910433706752160179501 3059216412640032060067313)
                  ·
                    refine ⟨2294412309480024045050485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3059216412640032060067313 2294412309480024045050485)
                    ·
                      refine ⟨215101154013752254223483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2294412309480024045050485 215101154013752254223483)
                      ·
                        rfl

theorem cell23_418908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_418908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418908 prefixEnd_418908 := by exact prefixLift 418908
  have htrace : WordTrace (prefixWord ++ tailWord_418908) baseStart_418908 baseEnd_418908 := by
    simpa [prefixWord, tailWord_418908, baseEnd_418908] using wordTrace_append hprefix tailTrace_418908
  have hstable : (prefixWord ++ tailWord_418908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418908).length < 2 ^ (prefixWord ++ tailWord_418908).sum := by decide
  have hdescent : baseEnd_418908 < baseStart_418908 := by decide
  rcases family_descends (prefixWord ++ tailWord_418908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418935 : List Nat := [1, 1, 3, 1, 1, 4, 3, 1, 2, 4, 2]
def baseStart_418935 : Nat := 118140960795 + 418935 * 2 ^ 59
def prefixEnd_418935 : Nat := 4983230072969 + 3 ^ 40 * 418935 * 2
def baseEnd_418935 : Nat := 215115017991423648585859

theorem tailTrace_418935 : CollatzResearch.WordTrace tailWord_418935 prefixEnd_418935 215115017991423648585859 := by
  unfold tailWord_418935
  simp only [CollatzResearch.WordTrace]
  refine ⟨15279814737277518246850259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10186543158185012164566839 15279814737277518246850259)
  ·
    refine ⟨22919722105916277370275389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15279814737277518246850259 22919722105916277370275389)
    ·
      refine ⟨8594895789718604013853271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22919722105916277370275389 8594895789718604013853271)
      ·
        refine ⟨12892343684577906020779907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8594895789718604013853271 12892343684577906020779907)
        ·
          refine ⟨19338515526866859031169861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12892343684577906020779907 19338515526866859031169861)
          ·
            refine ⟨3625971661287536068344349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19338515526866859031169861 3625971661287536068344349)
            ·
              refine ⟨1359739372982826025629131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3625971661287536068344349 1359739372982826025629131)
              ·
                refine ⟨2039609059474239038443697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1359739372982826025629131 2039609059474239038443697)
                ·
                  refine ⟨1529706794605679278832773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2039609059474239038443697 1529706794605679278832773)
                  ·
                    refine ⟨286820023988564864781145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1529706794605679278832773 286820023988564864781145)
                    ·
                      refine ⟨215115017991423648585859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 286820023988564864781145 215115017991423648585859)
                      ·
                        rfl

theorem cell23_418935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 4, 2].length) (baseStart_418935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418935 prefixEnd_418935 := by exact prefixLift 418935
  have htrace : WordTrace (prefixWord ++ tailWord_418935) baseStart_418935 baseEnd_418935 := by
    simpa [prefixWord, tailWord_418935, baseEnd_418935] using wordTrace_append hprefix tailTrace_418935
  have hstable : (prefixWord ++ tailWord_418935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418935).length < 2 ^ (prefixWord ++ tailWord_418935).sum := by decide
  have hdescent : baseEnd_418935 < baseStart_418935 := by decide
  rcases family_descends (prefixWord ++ tailWord_418935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418945 : List Nat := [1, 2, 4, 2, 2, 1, 1, 1, 5, 4]
def baseStart_418945 : Nat := 118140960795 + 418945 * 2 ^ 59
def prefixEnd_418945 : Nat := 4983230072969 + 3 ^ 40 * 418945 * 2
def baseEnd_418945 : Nat := 71706717599322869820271

theorem tailTrace_418945 : CollatzResearch.WordTrace tailWord_418945 prefixEnd_418945 71706717599322869820271 := by
  unfold tailWord_418945
  simp only [CollatzResearch.WordTrace]
  refine ⟨15280179467241289954714289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10186786311494193303142859 15280179467241289954714289)
  ·
    refine ⟨11460134600430967466035717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15280179467241289954714289 11460134600430967466035717)
    ·
      refine ⟨2148775237580806399881697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11460134600430967466035717 2148775237580806399881697)
      ·
        refine ⟨1611581428185604799911273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2148775237580806399881697 1611581428185604799911273)
        ·
          refine ⟨1208686071139203599933455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1611581428185604799911273 1208686071139203599933455)
          ·
            refine ⟨1813029106708805399900183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1208686071139203599933455 1813029106708805399900183)
            ·
              refine ⟨2719543660063208099850275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1813029106708805399900183 2719543660063208099850275)
              ·
                refine ⟨4079315490094812149775413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2719543660063208099850275 4079315490094812149775413)
                ·
                  refine ⟨382435827196388639041445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4079315490094812149775413 382435827196388639041445)
                  ·
                    refine ⟨71706717599322869820271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 382435827196388639041445 71706717599322869820271)
                    ·
                      rfl

theorem cell23_418945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_418945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418945 prefixEnd_418945 := by exact prefixLift 418945
  have htrace : WordTrace (prefixWord ++ tailWord_418945) baseStart_418945 baseEnd_418945 := by
    simpa [prefixWord, tailWord_418945, baseEnd_418945] using wordTrace_append hprefix tailTrace_418945
  have hstable : (prefixWord ++ tailWord_418945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418945).length < 2 ^ (prefixWord ++ tailWord_418945).sum := by decide
  have hdescent : baseEnd_418945 < baseStart_418945 := by decide
  rcases family_descends (prefixWord ++ tailWord_418945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418975 : List Nat := [1, 1, 2, 6, 2, 1, 1, 1, 8]
def baseStart_418975 : Nat := 118140960795 + 418975 * 2 ^ 59
def prefixEnd_418975 : Nat := 4983230072969 + 3 ^ 40 * 418975 * 2
def baseEnd_418975 : Nat := 23903950801955943565075

theorem tailTrace_418975 : CollatzResearch.WordTrace tailWord_418975 prefixEnd_418975 23903950801955943565075 := by
  unfold tailWord_418975
  simp only [CollatzResearch.WordTrace]
  refine ⟨15281273657132605078306379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10187515771421736718870919 15281273657132605078306379)
  ·
    refine ⟨22921910485698907617459569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15281273657132605078306379 22921910485698907617459569)
    ·
      refine ⟨17191432864274180713094677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22921910485698907617459569 17191432864274180713094677)
      ·
        refine ⟨805848415512852220926313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17191432864274180713094677 805848415512852220926313)
        ·
          refine ⟨604386311634639165694735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 805848415512852220926313 604386311634639165694735)
          ·
            refine ⟨906579467451958748542103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604386311634639165694735 906579467451958748542103)
            ·
              refine ⟨1359869201177938122813155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 906579467451958748542103 1359869201177938122813155)
              ·
                refine ⟨2039803801766907184219733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1359869201177938122813155 2039803801766907184219733)
                ·
                  refine ⟨23903950801955943565075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2039803801766907184219733 23903950801955943565075)
                  ·
                    rfl

theorem cell23_418975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 8].length) (baseStart_418975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418975 prefixEnd_418975 := by exact prefixLift 418975
  have htrace : WordTrace (prefixWord ++ tailWord_418975) baseStart_418975 baseEnd_418975 := by
    simpa [prefixWord, tailWord_418975, baseEnd_418975] using wordTrace_append hprefix tailTrace_418975
  have hstable : (prefixWord ++ tailWord_418975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418975).length < 2 ^ (prefixWord ++ tailWord_418975).sum := by decide
  have hdescent : baseEnd_418975 < baseStart_418975 := by decide
  rcases family_descends (prefixWord ++ tailWord_418975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418988 : List Nat := [2, 2, 1, 1, 1, 1, 1, 6, 3, 5]
def baseStart_418988 : Nat := 118140960795 + 418988 * 2 ^ 59
def prefixEnd_418988 : Nat := 4983230072969 + 3 ^ 40 * 418988 * 2
def baseEnd_418988 : Nat := 71714077488703980407705

theorem tailTrace_418988 : CollatzResearch.WordTrace tailWord_418988 prefixEnd_418988 71714077488703980407705 := by
  unfold tailWord_418988
  simp only [CollatzResearch.WordTrace]
  refine ⟨7640873903042754149264809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10187831870723672199019745 7640873903042754149264809)
  ·
    refine ⟨5730655427282065611948607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7640873903042754149264809 5730655427282065611948607)
    ·
      refine ⟨8595983140923098417922911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5730655427282065611948607 8595983140923098417922911)
      ·
        refine ⟨12893974711384647626884367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8595983140923098417922911 12893974711384647626884367)
        ·
          refine ⟨19340962067076971440326551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12893974711384647626884367 19340962067076971440326551)
          ·
            refine ⟨29011443100615457160489827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19340962067076971440326551 29011443100615457160489827)
            ·
              refine ⟨43517164650923185740734741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29011443100615457160489827 43517164650923185740734741)
              ·
                refine ⟨2039867093012024331596941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43517164650923185740734741 2039867093012024331596941)
                ·
                  refine ⟨764950159879509124348853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2039867093012024331596941 764950159879509124348853)
                  ·
                    refine ⟨71714077488703980407705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 764950159879509124348853 71714077488703980407705)
                    ·
                      rfl

theorem cell23_418988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 5].length) (baseStart_418988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418988 prefixEnd_418988 := by exact prefixLift 418988
  have htrace : WordTrace (prefixWord ++ tailWord_418988) baseStart_418988 baseEnd_418988 := by
    simpa [prefixWord, tailWord_418988, baseEnd_418988] using wordTrace_append hprefix tailTrace_418988
  have hstable : (prefixWord ++ tailWord_418988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418988).length < 2 ^ (prefixWord ++ tailWord_418988).sum := by decide
  have hdescent : baseEnd_418988 < baseStart_418988 := by decide
  rcases family_descends (prefixWord ++ tailWord_418988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418995 : List Nat := [1, 1, 1, 2, 3, 2, 3, 2, 1, 5, 2]
def baseStart_418995 : Nat := 118140960795 + 418995 * 2 ^ 59
def prefixEnd_418995 : Nat := 4983230072969 + 3 ^ 40 * 418995 * 2
def baseEnd_418995 : Nat := 215145826830693413835583

theorem tailTrace_418995 : CollatzResearch.WordTrace tailWord_418995 prefixEnd_418995 215145826830693413835583 := by
  unfold tailWord_418995
  simp only [CollatzResearch.WordTrace]
  refine ⟨15282003117060148494034439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10188002078040098996022959 15282003117060148494034439)
  ·
    refine ⟨22923004675590222741051659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15282003117060148494034439 22923004675590222741051659)
    ·
      refine ⟨34384507013385334111577489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22923004675590222741051659 34384507013385334111577489)
      ·
        refine ⟨25788380260039000583683117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34384507013385334111577489 25788380260039000583683117)
        ·
          refine ⟨9670642597514625218881169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25788380260039000583683117 9670642597514625218881169)
          ·
            refine ⟨7252981948135968914160877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9670642597514625218881169 7252981948135968914160877)
            ·
              refine ⟨2719868230550988342810329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7252981948135968914160877 2719868230550988342810329)
              ·
                refine ⟨2039901172913241257107747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2719868230550988342810329 2039901172913241257107747)
                ·
                  refine ⟨3059851759369861885661621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2039901172913241257107747 3059851759369861885661621)
                  ·
                    refine ⟨286861102440924551780777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3059851759369861885661621 286861102440924551780777)
                    ·
                      refine ⟨215145826830693413835583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 286861102440924551780777 215145826830693413835583)
                      ·
                        rfl

theorem cell23_418995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 5, 2].length) (baseStart_418995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_418995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_418995 prefixEnd_418995 := by exact prefixLift 418995
  have htrace : WordTrace (prefixWord ++ tailWord_418995) baseStart_418995 baseEnd_418995 := by
    simpa [prefixWord, tailWord_418995, baseEnd_418995] using wordTrace_append hprefix tailTrace_418995
  have hstable : (prefixWord ++ tailWord_418995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418995).length < 2 ^ (prefixWord ++ tailWord_418995).sum := by decide
  have hdescent : baseEnd_418995 < baseStart_418995 := by decide
  rcases family_descends (prefixWord ++ tailWord_418995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419005 : List Nat := [1, 4, 1, 2, 1, 1, 3, 4, 1, 5]
def baseStart_419005 : Nat := 118140960795 + 419005 * 2 ^ 59
def prefixEnd_419005 : Nat := 4983230072969 + 3 ^ 40 * 419005 * 2
def baseEnd_419005 : Nat := 71716987212412791570179

theorem tailTrace_419005 : CollatzResearch.WordTrace tailWord_419005 prefixEnd_419005 71716987212412791570179 := by
  unfold tailWord_419005
  simp only [CollatzResearch.WordTrace]
  refine ⟨15282367847023920201898469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10188245231349280134598979 15282367847023920201898469)
  ·
    refine ⟨2865443971316985037855963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15282367847023920201898469 2865443971316985037855963)
    ·
      refine ⟨4298165956975477556783945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2865443971316985037855963 4298165956975477556783945)
      ·
        refine ⟨3223624467731608167587959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4298165956975477556783945 3223624467731608167587959)
        ·
          refine ⟨4835436701597412251381939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3223624467731608167587959 4835436701597412251381939)
          ·
            refine ⟨7253155052396118377072909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4835436701597412251381939 7253155052396118377072909)
            ·
              refine ⟨2719933144648544391402341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7253155052396118377072909 2719933144648544391402341)
              ·
                refine ⟨509987464621602073387939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2719933144648544391402341 509987464621602073387939)
                ·
                  refine ⟨764981196932403110081909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 509987464621602073387939 764981196932403110081909)
                  ·
                    refine ⟨71716987212412791570179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 764981196932403110081909 71716987212412791570179)
                    ·
                      rfl

theorem cell23_419005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 5].length) (baseStart_419005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_419005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_419005 prefixEnd_419005 := by exact prefixLift 419005
  have htrace : WordTrace (prefixWord ++ tailWord_419005) baseStart_419005 baseEnd_419005 := by
    simpa [prefixWord, tailWord_419005, baseEnd_419005] using wordTrace_append hprefix tailTrace_419005
  have hstable : (prefixWord ++ tailWord_419005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419005).length < 2 ^ (prefixWord ++ tailWord_419005).sum := by decide
  have hdescent : baseEnd_419005 < baseStart_419005 := by decide
  rcases family_descends (prefixWord ++ tailWord_419005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419029 : List Nat := [1, 3, 2, 4, 1, 2, 1, 2, 2, 3, 2]
def baseStart_419029 : Nat := 118140960795 + 419029 * 2 ^ 59
def prefixEnd_419029 : Nat := 4983230072969 + 3 ^ 40 * 419029 * 2
def baseEnd_419029 : Nat := 215163285172946280810427

theorem tailTrace_419029 : CollatzResearch.WordTrace tailWord_419029 prefixEnd_419029 215163285172946280810427 := by
  unfold tailWord_419029
  simp only [CollatzResearch.WordTrace]
  refine ⟨15283243198936972300772141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10188828799291314867181427 15283243198936972300772141)
  ·
    refine ⟨5731216199601364612789553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15283243198936972300772141 5731216199601364612789553)
    ·
      refine ⟨4298412149701023459592165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5731216199601364612789553 4298412149701023459592165)
      ·
        refine ⟨805952278068941898673531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4298412149701023459592165 805952278068941898673531)
        ·
          refine ⟨1208928417103412848010297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 805952278068941898673531 1208928417103412848010297)
          ·
            refine ⟨906696312827559636007723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1208928417103412848010297 906696312827559636007723)
            ·
              refine ⟨1360044469241339454011585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 906696312827559636007723 1360044469241339454011585)
              ·
                refine ⟨1020033351931004590508689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1360044469241339454011585 1020033351931004590508689)
                ·
                  refine ⟨765025013948253442881517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1020033351931004590508689 765025013948253442881517)
                  ·
                    refine ⟨286884380230595041080569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 765025013948253442881517 286884380230595041080569)
                    ·
                      refine ⟨215163285172946280810427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 286884380230595041080569 215163285172946280810427)
                      ·
                        rfl

theorem cell23_419029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_419029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_419029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_419029 prefixEnd_419029 := by exact prefixLift 419029
  have htrace : WordTrace (prefixWord ++ tailWord_419029) baseStart_419029 baseEnd_419029 := by
    simpa [prefixWord, tailWord_419029, baseEnd_419029] using wordTrace_append hprefix tailTrace_419029
  have hstable : (prefixWord ++ tailWord_419029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419029).length < 2 ^ (prefixWord ++ tailWord_419029).sum := by decide
  have hdescent : baseEnd_419029 < baseStart_419029 := by decide
  rcases family_descends (prefixWord ++ tailWord_419029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419052 : List Nat := [2, 2, 1, 1, 2, 5, 1, 3, 2, 4]
def baseStart_419052 : Nat := 118140960795 + 419052 * 2 ^ 59
def prefixEnd_419052 : Nat := 4983230072969 + 3 ^ 40 * 419052 * 2
def baseEnd_419052 : Nat := 71725031742666563607607

theorem tailTrace_419052 : CollatzResearch.WordTrace tailWord_419052 prefixEnd_419052 71725031742666563607607 := by
  unfold tailWord_419052
  simp only [CollatzResearch.WordTrace]
  refine ⟨7642041038926823614429705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10189388051902431485906273 7642041038926823614429705)
  ·
    refine ⟨5731530779195117710822279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7642041038926823614429705 5731530779195117710822279)
    ·
      refine ⟨8597296168792676566233419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5731530779195117710822279 8597296168792676566233419)
      ·
        refine ⟨12895944253189014849350129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8597296168792676566233419 12895944253189014849350129)
        ·
          refine ⟨9671958189891761137012597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12895944253189014849350129 9671958189891761137012597)
          ·
            refine ⟨906746080302352606594931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9671958189891761137012597 906746080302352606594931)
            ·
              refine ⟨1360119120453528909892397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 906746080302352606594931 1360119120453528909892397)
              ·
                refine ⟨510044670170073341209649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1360119120453528909892397 510044670170073341209649)
                ·
                  refine ⟨382533502627555005907237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 510044670170073341209649 382533502627555005907237)
                  ·
                    refine ⟨71725031742666563607607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 382533502627555005907237 71725031742666563607607)
                    ·
                      rfl

theorem cell23_419052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 4].length) (baseStart_419052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_419052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_419052 prefixEnd_419052 := by exact prefixLift 419052
  have htrace : WordTrace (prefixWord ++ tailWord_419052) baseStart_419052 baseEnd_419052 := by
    simpa [prefixWord, tailWord_419052, baseEnd_419052] using wordTrace_append hprefix tailTrace_419052
  have hstable : (prefixWord ++ tailWord_419052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419052).length < 2 ^ (prefixWord ++ tailWord_419052).sum := by decide
  have hdescent : baseEnd_419052 < baseStart_419052 := by decide
  rcases family_descends (prefixWord ++ tailWord_419052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419075 : List Nat := [1, 1, 1, 3, 2, 4, 1, 1, 3, 3, 3]
def baseStart_419075 : Nat := 118140960795 + 419075 * 2 ^ 59
def prefixEnd_419075 : Nat := 4983230072969 + 3 ^ 40 * 419075 * 2
def baseEnd_419075 : Nat := 215186905283053100835215

theorem tailTrace_419075 : CollatzResearch.WordTrace tailWord_419075 prefixEnd_419075 215186905283053100835215 := by
  unfold tailWord_419075
  simp only [CollatzResearch.WordTrace]
  refine ⟨15284920956770322156946679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10189947304513548104631119 15284920956770322156946679)
  ·
    refine ⟨22927381435155483235420019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15284920956770322156946679 22927381435155483235420019)
    ·
      refine ⟨34391072152733224853130029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22927381435155483235420019 34391072152733224853130029)
      ·
        refine ⟨12896652057274959319923761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34391072152733224853130029 12896652057274959319923761)
        ·
          refine ⟨9672489042956219489942821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12896652057274959319923761 9672489042956219489942821)
          ·
            refine ⟨1813591695554291154364279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9672489042956219489942821 1813591695554291154364279)
            ·
              refine ⟨2720387543331436731546419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1813591695554291154364279 2720387543331436731546419)
              ·
                refine ⟨4080581314997155097319629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2720387543331436731546419 4080581314997155097319629)
                ·
                  refine ⟨1530217993123933161494861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4080581314997155097319629 1530217993123933161494861)
                  ·
                    refine ⟨573831747421474935560573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1530217993123933161494861 573831747421474935560573)
                    ·
                      refine ⟨215186905283053100835215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 573831747421474935560573 215186905283053100835215)
                      ·
                        rfl

theorem cell23_419075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 3, 3].length) (baseStart_419075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_419075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_419075 prefixEnd_419075 := by exact prefixLift 419075
  have htrace : WordTrace (prefixWord ++ tailWord_419075) baseStart_419075 baseEnd_419075 := by
    simpa [prefixWord, tailWord_419075, baseEnd_419075] using wordTrace_append hprefix tailTrace_419075
  have hstable : (prefixWord ++ tailWord_419075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419075).length < 2 ^ (prefixWord ++ tailWord_419075).sum := by decide
  have hdescent : baseEnd_419075 < baseStart_419075 := by decide
  rcases family_descends (prefixWord ++ tailWord_419075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419088 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 5]
def baseStart_419088 : Nat := 118140960795 + 419088 * 2 ^ 59
def prefixEnd_419088 : Nat := 4983230072969 + 3 ^ 40 * 419088 * 2
def baseEnd_419088 : Nat := 215193580531561549972655

theorem tailTrace_419088 : CollatzResearch.WordTrace tailWord_419088 prefixEnd_419088 215193580531561549972655 := by
  unfold tailWord_419088
  simp only [CollatzResearch.WordTrace]
  refine ⟨7642697552861612688584959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10190263403815483584779945 7642697552861612688584959)
  ·
    refine ⟨11464046329292419032877439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7642697552861612688584959 11464046329292419032877439)
    ·
      refine ⟨17196069493938628549316159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11464046329292419032877439 17196069493938628549316159)
      ·
        refine ⟨25794104240907942823974239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17196069493938628549316159 25794104240907942823974239)
        ·
          refine ⟨38691156361361914235961359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25794104240907942823974239 38691156361361914235961359)
          ·
            refine ⟨58036734542042871353942039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38691156361361914235961359 58036734542042871353942039)
            ·
              refine ⟨87055101813064307030913059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58036734542042871353942039 87055101813064307030913059)
              ·
                refine ⟨130582652719596460546369589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87055101813064307030913059 130582652719596460546369589)
                ·
                  refine ⟨12242123692462168176222149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130582652719596460546369589 12242123692462168176222149)
                  ·
                    refine ⟨2295398192336656533041653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12242123692462168176222149 2295398192336656533041653)
                    ·
                      refine ⟨215193580531561549972655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2295398192336656533041653 215193580531561549972655)
                      ·
                        rfl

theorem cell23_419088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 5].length) (baseStart_419088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_419088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_419088 prefixEnd_419088 := by exact prefixLift 419088
  have htrace : WordTrace (prefixWord ++ tailWord_419088) baseStart_419088 baseEnd_419088 := by
    simpa [prefixWord, tailWord_419088, baseEnd_419088] using wordTrace_append hprefix tailTrace_419088
  have hstable : (prefixWord ++ tailWord_419088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419088).length < 2 ^ (prefixWord ++ tailWord_419088).sum := by decide
  have hdescent : baseEnd_419088 < baseStart_419088 := by decide
  rcases family_descends (prefixWord ++ tailWord_419088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419109 : List Nat := [1, 3, 1, 2, 4, 1, 2, 3, 2, 1, 3]
def baseStart_419109 : Nat := 118140960795 + 419109 * 2 ^ 59
def prefixEnd_419109 : Nat := 4983230072969 + 3 ^ 40 * 419109 * 2
def baseEnd_419109 : Nat := 215204363625305967810059

theorem tailTrace_419109 : CollatzResearch.WordTrace tailWord_419109 prefixEnd_419109 215204363625305967810059 := by
  unfold tailWord_419109
  simp only [CollatzResearch.WordTrace]
  refine ⟨15286161038647145963684381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10190774025764763975789587 15286161038647145963684381)
  ·
    refine ⟨5732310389492679736381643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15286161038647145963684381 5732310389492679736381643)
    ·
      refine ⟨8598465584239019604572465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5732310389492679736381643 8598465584239019604572465)
      ·
        refine ⟨6448849188179264703429349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8598465584239019604572465 6448849188179264703429349)
        ·
          refine ⟨1209159222783612131893003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6448849188179264703429349 1209159222783612131893003)
          ·
            refine ⟨1813738834175418197839505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1209159222783612131893003 1813738834175418197839505)
            ·
              refine ⟨1360304125631563648379629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1813738834175418197839505 1360304125631563648379629)
              ·
                refine ⟨510114047111836368142361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1360304125631563648379629 510114047111836368142361)
                ·
                  refine ⟨382585535333877276106771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 510114047111836368142361 382585535333877276106771)
                  ·
                    refine ⟨573878303000815914160157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 382585535333877276106771 573878303000815914160157)
                    ·
                      refine ⟨215204363625305967810059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 573878303000815914160157 215204363625305967810059)
                      ·
                        rfl

theorem cell23_419109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 2, 1, 3].length) (baseStart_419109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_419109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_419109 prefixEnd_419109 := by exact prefixLift 419109
  have htrace : WordTrace (prefixWord ++ tailWord_419109) baseStart_419109 baseEnd_419109 := by
    simpa [prefixWord, tailWord_419109, baseEnd_419109] using wordTrace_append hprefix tailTrace_419109
  have hstable : (prefixWord ++ tailWord_419109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419109).length < 2 ^ (prefixWord ++ tailWord_419109).sum := by decide
  have hdescent : baseEnd_419109 < baseStart_419109 := by decide
  rcases family_descends (prefixWord ++ tailWord_419109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419145 : List Nat := [1, 2, 1, 1, 2, 3, 3, 2, 2, 2, 4]
def baseStart_419145 : Nat := 118140960795 + 419145 * 2 ^ 59
def prefixEnd_419145 : Nat := 4983230072969 + 3 ^ 40 * 419145 * 2
def baseEnd_419145 : Nat := 215222848928867826959893

theorem tailTrace_419145 : CollatzResearch.WordTrace tailWord_419145 prefixEnd_419145 215222848928867826959893 := by
  unfold tailWord_419145
  simp only [CollatzResearch.WordTrace]
  refine ⟨15287474066516724111994889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10191649377677816074663259 15287474066516724111994889)
  ·
    refine ⟨11465605549887543083996167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15287474066516724111994889 11465605549887543083996167)
    ·
      refine ⟨17198408324831314625994251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11465605549887543083996167 17198408324831314625994251)
      ·
        refine ⟨25797612487246971938991377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17198408324831314625994251 25797612487246971938991377)
        ·
          refine ⟨19348209365435228954243533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25797612487246971938991377 19348209365435228954243533)
          ·
            refine ⟨7255578512038210857841325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19348209365435228954243533 7255578512038210857841325)
            ·
              refine ⟨2720841942014329071690497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7255578512038210857841325 2720841942014329071690497)
              ·
                refine ⟨2040631456510746803767873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2720841942014329071690497 2040631456510746803767873)
                ·
                  refine ⟨1530473592383060102825905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2040631456510746803767873 1530473592383060102825905)
                  ·
                    refine ⟨1147855194287295077119429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1530473592383060102825905 1147855194287295077119429)
                    ·
                      refine ⟨215222848928867826959893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1147855194287295077119429 215222848928867826959893)
                      ·
                        rfl

theorem cell23_419145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 2, 4].length) (baseStart_419145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_419145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_419145 prefixEnd_419145 := by exact prefixLift 419145
  have htrace : WordTrace (prefixWord ++ tailWord_419145) baseStart_419145 baseEnd_419145 := by
    simpa [prefixWord, tailWord_419145, baseEnd_419145] using wordTrace_append hprefix tailTrace_419145
  have hstable : (prefixWord ++ tailWord_419145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419145).length < 2 ^ (prefixWord ++ tailWord_419145).sum := by decide
  have hdescent : baseEnd_419145 < baseStart_419145 := by decide
  rcases family_descends (prefixWord ++ tailWord_419145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419155 : List Nat := [1, 1, 1, 2, 1, 1, 8, 1, 7]
def baseStart_419155 : Nat := 118140960795 + 419155 * 2 ^ 59
def prefixEnd_419155 : Nat := 4983230072969 + 3 ^ 40 * 419155 * 2
def baseEnd_419155 : Nat := 23914220415045865314983

theorem tailTrace_419155 : CollatzResearch.WordTrace tailWord_419155 prefixEnd_419155 23914220415045865314983 := by
  unfold tailWord_419155
  simp only [CollatzResearch.WordTrace]
  refine ⟨15287838796480495819858919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10191892530986997213239279 15287838796480495819858919)
  ·
    refine ⟨22931758194720743729788379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15287838796480495819858919 22931758194720743729788379)
    ·
      refine ⟨34397637292081115594682569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22931758194720743729788379 34397637292081115594682569)
      ·
        refine ⟨25798227969060836696011927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34397637292081115594682569 25798227969060836696011927)
        ·
          refine ⟨38697341953591255044017891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25798227969060836696011927 38697341953591255044017891)
          ·
            refine ⟨58046012930386882566026837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38697341953591255044017891 58046012930386882566026837)
            ·
              refine ⟨680226714027971280070627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 58046012930386882566026837 680226714027971280070627)
              ·
                refine ⟨1020340071041956920105941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 680226714027971280070627 1020340071041956920105941)
                ·
                  refine ⟨23914220415045865314983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1020340071041956920105941 23914220415045865314983)
                  ·
                    rfl

theorem cell23_419155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 7].length) (baseStart_419155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_419155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_419155 prefixEnd_419155 := by exact prefixLift 419155
  have htrace : WordTrace (prefixWord ++ tailWord_419155) baseStart_419155 baseEnd_419155 := by
    simpa [prefixWord, tailWord_419155, baseEnd_419155] using wordTrace_append hprefix tailTrace_419155
  have hstable : (prefixWord ++ tailWord_419155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419155).length < 2 ^ (prefixWord ++ tailWord_419155).sum := by decide
  have hdescent : baseEnd_419155 < baseStart_419155 := by decide
  rcases family_descends (prefixWord ++ tailWord_419155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419185 : List Nat := [1, 2, 2, 2, 1, 2, 4, 1, 1, 7]
def baseStart_419185 : Nat := 118140960795 + 419185 * 2 ^ 59
def prefixEnd_419185 : Nat := 4983230072969 + 3 ^ 40 * 419185 * 2
def baseEnd_419185 : Nat := 71747796051682556819903

theorem tailTrace_419185 : CollatzResearch.WordTrace tailWord_419185 prefixEnd_419185 71747796051682556819903 := by
  unfold tailWord_419185
  simp only [CollatzResearch.WordTrace]
  refine ⟨15288932986371810943451009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10192621990914540628967339 15288932986371810943451009)
  ·
    refine ⟨11466699739778858207588257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15288932986371810943451009 11466699739778858207588257)
    ·
      refine ⟨8600024804834143655691193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11466699739778858207588257 8600024804834143655691193)
      ·
        refine ⟨6450018603625607741768395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8600024804834143655691193 6450018603625607741768395)
        ·
          refine ⟨9675027905438411612652593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6450018603625607741768395 9675027905438411612652593)
          ·
            refine ⟨7256270929078808709489445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9675027905438411612652593 7256270929078808709489445)
            ·
              refine ⟨1360550799202276633029271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7256270929078808709489445 1360550799202276633029271)
              ·
                refine ⟨2040826198803414949543907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1360550799202276633029271 2040826198803414949543907)
                ·
                  refine ⟨3061239298205122424315861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2040826198803414949543907 3061239298205122424315861)
                  ·
                    refine ⟨71747796051682556819903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3061239298205122424315861 71747796051682556819903)
                    ·
                      rfl

theorem cell23_419185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 7].length) (baseStart_419185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_419185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_419185 prefixEnd_419185 := by exact prefixLift 419185
  have htrace : WordTrace (prefixWord ++ tailWord_419185) baseStart_419185 baseEnd_419185 := by
    simpa [prefixWord, tailWord_419185, baseEnd_419185] using wordTrace_append hprefix tailTrace_419185
  have hstable : (prefixWord ++ tailWord_419185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419185).length < 2 ^ (prefixWord ++ tailWord_419185).sum := by decide
  have hdescent : baseEnd_419185 < baseStart_419185 := by decide
  rcases family_descends (prefixWord ++ tailWord_419185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419195 : List Nat := [1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 5]
def baseStart_419195 : Nat := 118140960795 + 419195 * 2 ^ 59
def prefixEnd_419195 : Nat := 4983230072969 + 3 ^ 40 * 419195 * 2
def baseEnd_419195 : Nat := 215248522961592631334663

theorem tailTrace_419195 : CollatzResearch.WordTrace tailWord_419195 prefixEnd_419195 215248522961592631334663 := by
  unfold tailWord_419195
  simp only [CollatzResearch.WordTrace]
  refine ⟨15289297716335582651315039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10192865144223721767543359 15289297716335582651315039)
  ·
    refine ⟨22933946574503373976972559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15289297716335582651315039 22933946574503373976972559)
    ·
      refine ⟨34400919861755060965458839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22933946574503373976972559 34400919861755060965458839)
      ·
        refine ⟨51601379792632591448188259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34400919861755060965458839 51601379792632591448188259)
        ·
          refine ⟨77402069688948887172282389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51601379792632591448188259 77402069688948887172282389)
          ·
            refine ⟨3628222016669479086200737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 77402069688948887172282389 3628222016669479086200737)
            ·
              refine ⟨2721166512502109314650553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3628222016669479086200737 2721166512502109314650553)
              ·
                refine ⟨2040874884376581985987915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2721166512502109314650553 2040874884376581985987915)
                ·
                  refine ⟨3061312326564872978981873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2040874884376581985987915 3061312326564872978981873)
                  ·
                    refine ⟨2295984244923654734236405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3061312326564872978981873 2295984244923654734236405)
                    ·
                      refine ⟨215248522961592631334663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2295984244923654734236405 215248522961592631334663)
                      ·
                        rfl

theorem cell23_419195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 5].length) (baseStart_419195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_419195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_419195 prefixEnd_419195 := by exact prefixLift 419195
  have htrace : WordTrace (prefixWord ++ tailWord_419195) baseStart_419195 baseEnd_419195 := by
    simpa [prefixWord, tailWord_419195, baseEnd_419195] using wordTrace_append hprefix tailTrace_419195
  have hstable : (prefixWord ++ tailWord_419195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419195).length < 2 ^ (prefixWord ++ tailWord_419195).sum := by decide
  have hdescent : baseEnd_419195 < baseStart_419195 := by decide
  rcases family_descends (prefixWord ++ tailWord_419195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419232 : List Nat := [2, 1, 1, 4, 1, 2, 2, 1, 5, 4]
def baseStart_419232 : Nat := 118140960795 + 419232 * 2 ^ 59
def prefixEnd_419232 : Nat := 4983230072969 + 3 ^ 40 * 419232 * 2
def baseEnd_419232 : Nat := 71755840581936328857331

theorem tailTrace_419232 : CollatzResearch.WordTrace tailWord_419232 prefixEnd_419232 71755840581936328857331 := by
  unfold tailWord_419232
  simp only [CollatzResearch.WordTrace]
  refine ⟨7645323608600768985205975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10193764811467691980274633 7645323608600768985205975)
  ·
    refine ⟨11467985412901153477808963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7645323608600768985205975 11467985412901153477808963)
    ·
      refine ⟨17201978119351730216713445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11467985412901153477808963 17201978119351730216713445)
      ·
        refine ⟨3225370897378449415633771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17201978119351730216713445 3225370897378449415633771)
        ·
          refine ⟨4838056346067674123450657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3225370897378449415633771 4838056346067674123450657)
          ·
            refine ⟨3628542259550755592587993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4838056346067674123450657 3628542259550755592587993)
            ·
              refine ⟨2721406694663066694440995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3628542259550755592587993 2721406694663066694440995)
              ·
                refine ⟨4082110041994600041661493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2721406694663066694440995 4082110041994600041661493)
                ·
                  refine ⟨382697816436993753905765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4082110041994600041661493 382697816436993753905765)
                  ·
                    refine ⟨71755840581936328857331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 382697816436993753905765 71755840581936328857331)
                    ·
                      rfl

theorem cell23_419232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 5, 4].length) (baseStart_419232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_419232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_419232 prefixEnd_419232 := by exact prefixLift 419232
  have htrace : WordTrace (prefixWord ++ tailWord_419232) baseStart_419232 baseEnd_419232 := by
    simpa [prefixWord, tailWord_419232, baseEnd_419232] using wordTrace_append hprefix tailTrace_419232
  have hstable : (prefixWord ++ tailWord_419232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419232).length < 2 ^ (prefixWord ++ tailWord_419232).sum := by decide
  have hdescent : baseEnd_419232 < baseStart_419232 := by decide
  rcases family_descends (prefixWord ++ tailWord_419232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419239 : List Nat := [1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 4]
def baseStart_419239 : Nat := 118140960795 + 419239 * 2 ^ 59
def prefixEnd_419239 : Nat := 4983230072969 + 3 ^ 40 * 419239 * 2
def baseEnd_419239 : Nat := 215271116110390459184461

theorem tailTrace_419239 : CollatzResearch.WordTrace tailWord_419239 prefixEnd_419239 215271116110390459184461 := by
  unfold tailWord_419239
  simp only [CollatzResearch.WordTrace]
  refine ⟨15290902528176178165916771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10193935018784118777277847 15290902528176178165916771)
  ·
    refine ⟨22936353792264267248875157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15290902528176178165916771 22936353792264267248875157)
    ·
      refine ⟨1075141584012387527291023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22936353792264267248875157 1075141584012387527291023)
      ·
        refine ⟨1612712376018581290936535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1075141584012387527291023 1612712376018581290936535)
        ·
          refine ⟨2419068564027871936404803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1612712376018581290936535 2419068564027871936404803)
          ·
            refine ⟨3628602846041807904607205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2419068564027871936404803 3628602846041807904607205)
            ·
              refine ⟨680363033632838982113851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3628602846041807904607205 680363033632838982113851)
              ·
                refine ⟨1020544550449258473170777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 680363033632838982113851 1020544550449258473170777)
                ·
                  refine ⟨765408412836943854878083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1020544550449258473170777 765408412836943854878083)
                  ·
                    refine ⟨1148112619255415782317125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 765408412836943854878083 1148112619255415782317125)
                    ·
                      refine ⟨215271116110390459184461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1148112619255415782317125 215271116110390459184461)
                      ·
                        rfl

theorem cell23_419239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_419239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_419239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_419239 prefixEnd_419239 := by exact prefixLift 419239
  have htrace : WordTrace (prefixWord ++ tailWord_419239) baseStart_419239 baseEnd_419239 := by
    simpa [prefixWord, tailWord_419239, baseEnd_419239] using wordTrace_append hprefix tailTrace_419239
  have hstable : (prefixWord ++ tailWord_419239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419239).length < 2 ^ (prefixWord ++ tailWord_419239).sum := by decide
  have hdescent : baseEnd_419239 < baseStart_419239 := by decide
  rcases family_descends (prefixWord ++ tailWord_419239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419289 : List Nat := [1, 2, 1, 2, 4, 2, 1, 1, 5, 1, 3]
def baseStart_419289 : Nat := 118140960795 + 419289 * 2 ^ 59
def prefixEnd_419289 : Nat := 4983230072969 + 3 ^ 40 * 419289 * 2
def baseEnd_419289 : Nat := 215296790143115263559231

theorem tailTrace_419289 : CollatzResearch.WordTrace tailWord_419289 prefixEnd_419289 215296790143115263559231 := by
  unfold tailWord_419289
  simp only [CollatzResearch.WordTrace]
  refine ⟨15292726177995036705236921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10195150785330024470157947 15292726177995036705236921)
  ·
    refine ⟨11469544633496277528927691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15292726177995036705236921 11469544633496277528927691)
    ·
      refine ⟨17204316950244416293391537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11469544633496277528927691 17204316950244416293391537)
      ·
        refine ⟨12903237712683312220043653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17204316950244416293391537 12903237712683312220043653)
        ·
          refine ⟨2419357071128121041258185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12903237712683312220043653 2419357071128121041258185)
          ·
            refine ⟨1814517803346090780943639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2419357071128121041258185 1814517803346090780943639)
            ·
              refine ⟨2721776705019136171415459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1814517803346090780943639 2721776705019136171415459)
              ·
                refine ⟨4082665057528704257123189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2721776705019136171415459 4082665057528704257123189)
                ·
                  refine ⟨382749849143316024105299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4082665057528704257123189 382749849143316024105299)
                  ·
                    refine ⟨574124773714974036157949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 382749849143316024105299 574124773714974036157949)
                    ·
                      refine ⟨215296790143115263559231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 574124773714974036157949 215296790143115263559231)
                      ·
                        rfl

theorem cell23_419289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 5, 1, 3].length) (baseStart_419289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_419289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_419289 prefixEnd_419289 := by exact prefixLift 419289
  have htrace : WordTrace (prefixWord ++ tailWord_419289) baseStart_419289 baseEnd_419289 := by
    simpa [prefixWord, tailWord_419289, baseEnd_419289] using wordTrace_append hprefix tailTrace_419289
  have hstable : (prefixWord ++ tailWord_419289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419289).length < 2 ^ (prefixWord ++ tailWord_419289).sum := by decide
  have hdescent : baseEnd_419289 < baseStart_419289 := by decide
  rcases family_descends (prefixWord ++ tailWord_419289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419305 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 2, 10]
def baseStart_419305 : Nat := 118140960795 + 419305 * 2 ^ 59
def prefixEnd_419305 : Nat := 4983230072969 + 3 ^ 40 * 419305 * 2
def baseEnd_419305 : Nat := 71768335277862400319719

theorem tailTrace_419305 : CollatzResearch.WordTrace tailWord_419305 prefixEnd_419305 71768335277862400319719 := by
  unfold tailWord_419305
  simp only [CollatzResearch.WordTrace]
  refine ⟨15293309745937071437819369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10195539830624714291879579 15293309745937071437819369)
  ·
    refine ⟨11469982309452803578364527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15293309745937071437819369 11469982309452803578364527)
    ·
      refine ⟨17204973464179205367546791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11469982309452803578364527 17204973464179205367546791)
      ·
        refine ⟨25807460196268808051320187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17204973464179205367546791 25807460196268808051320187)
        ·
          refine ⟨38711190294403212076980281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25807460196268808051320187 38711190294403212076980281)
          ·
            refine ⟨29033392720802409057735211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38711190294403212076980281 29033392720802409057735211)
            ·
              refine ⟨43550089081203613586602817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29033392720802409057735211 43550089081203613586602817)
              ·
                refine ⟨32662566810902710189952113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43550089081203613586602817 32662566810902710189952113)
                ·
                  refine ⟨24496925108177032642464085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32662566810902710189952113 24496925108177032642464085)
                  ·
                    refine ⟨71768335277862400319719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 24496925108177032642464085 71768335277862400319719)
                    ·
                      rfl

theorem cell23_419305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 10].length) (baseStart_419305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_419305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_419305 prefixEnd_419305 := by exact prefixLift 419305
  have htrace : WordTrace (prefixWord ++ tailWord_419305) baseStart_419305 baseEnd_419305 := by
    simpa [prefixWord, tailWord_419305, baseEnd_419305] using wordTrace_append hprefix tailTrace_419305
  have hstable : (prefixWord ++ tailWord_419305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419305).length < 2 ^ (prefixWord ++ tailWord_419305).sum := by decide
  have hdescent : baseEnd_419305 < baseStart_419305 := by decide
  rcases family_descends (prefixWord ++ tailWord_419305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419446 : List Nat := [5, 1, 1, 2, 2, 2, 1, 1, 2, 6]
def baseStart_419446 : Nat := 118140960795 + 419446 * 2 ^ 59
def prefixEnd_419446 : Nat := 4983230072969 + 3 ^ 40 * 419446 * 2
def baseEnd_419446 : Nat := 71792468868623716432003

theorem tailTrace_419446 : CollatzResearch.WordTrace tailWord_419446 prefixEnd_419446 71792468868623716432003 := by
  unfold tailWord_419446
  simp only [CollatzResearch.WordTrace]
  refine ⟨956153277401640782418887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10198968292284168345801461 956153277401640782418887)
  ·
    refine ⟨1434229916102461173628331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 956153277401640782418887 1434229916102461173628331)
    ·
      refine ⟨2151344874153691760442497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1434229916102461173628331 2151344874153691760442497)
      ·
        refine ⟨1613508655615268820331873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2151344874153691760442497 1613508655615268820331873)
        ·
          refine ⟨1210131491711451615248905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1613508655615268820331873 1210131491711451615248905)
          ·
            refine ⟨907598618783588711436679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1210131491711451615248905 907598618783588711436679)
            ·
              refine ⟨1361397928175383067155019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 907598618783588711436679 1361397928175383067155019)
              ·
                refine ⟨2042096892263074600732529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1361397928175383067155019 2042096892263074600732529)
                ·
                  refine ⟨1531572669197305950549397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2042096892263074600732529 1531572669197305950549397)
                  ·
                    refine ⟨71792468868623716432003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1531572669197305950549397 71792468868623716432003)
                    ·
                      rfl

theorem cell23_419446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_419446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_419446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_419446 prefixEnd_419446 := by exact prefixLift 419446
  have htrace : WordTrace (prefixWord ++ tailWord_419446) baseStart_419446 baseEnd_419446 := by
    simpa [prefixWord, tailWord_419446, baseEnd_419446] using wordTrace_append hprefix tailTrace_419446
  have hstable : (prefixWord ++ tailWord_419446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419446).length < 2 ^ (prefixWord ++ tailWord_419446).sum := by decide
  have hdescent : baseEnd_419446 < baseStart_419446 := by decide
  rcases family_descends (prefixWord ++ tailWord_419446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419449 : List Nat := [1, 2, 1, 3, 3, 1, 3, 1, 2, 2, 4]
def baseStart_419449 : Nat := 118140960795 + 419449 * 2 ^ 59
def prefixEnd_419449 : Nat := 4983230072969 + 3 ^ 40 * 419449 * 2
def baseEnd_419449 : Nat := 215378947047834637558495

theorem tailTrace_419449 : CollatzResearch.WordTrace tailWord_419449 prefixEnd_419449 215378947047834637558495 := by
  unfold tailWord_419449
  simp only [CollatzResearch.WordTrace]
  refine ⟨15298561857415384031061401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10199041238276922687374267 15298561857415384031061401)
  ·
    refine ⟨11473921393061538023296051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15298561857415384031061401 11473921393061538023296051)
    ·
      refine ⟨17210882089592307034944077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11473921393061538023296051 17210882089592307034944077)
      ·
        refine ⟨6454080783597115138104029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17210882089592307034944077 6454080783597115138104029)
        ·
          refine ⟨2420280293848918176789011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6454080783597115138104029 2420280293848918176789011)
          ·
            refine ⟨3630420440773377265183517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2420280293848918176789011 3630420440773377265183517)
            ·
              refine ⟨1361407665290016474443819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3630420440773377265183517 1361407665290016474443819)
              ·
                refine ⟨2042111497935024711665729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1361407665290016474443819 2042111497935024711665729)
                ·
                  refine ⟨1531583623451268533749297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2042111497935024711665729 1531583623451268533749297)
                  ·
                    refine ⟨1148687717588451400311973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1531583623451268533749297 1148687717588451400311973)
                    ·
                      refine ⟨215378947047834637558495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1148687717588451400311973 215378947047834637558495)
                      ·
                        rfl

theorem cell23_419449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_419449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_419449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_419449 prefixEnd_419449 := by exact prefixLift 419449
  have htrace : WordTrace (prefixWord ++ tailWord_419449) baseStart_419449 baseEnd_419449 := by
    simpa [prefixWord, tailWord_419449, baseEnd_419449] using wordTrace_append hprefix tailTrace_419449
  have hstable : (prefixWord ++ tailWord_419449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419449).length < 2 ^ (prefixWord ++ tailWord_419449).sum := by decide
  have hdescent : baseEnd_419449 < baseStart_419449 := by decide
  rcases family_descends (prefixWord ++ tailWord_419449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419453 : List Nat := [1, 4, 1, 1, 4, 2, 2, 1, 1, 4, 2]
def baseStart_419453 : Nat := 118140960795 + 419453 * 2 ^ 59
def prefixEnd_419453 : Nat := 4983230072969 + 3 ^ 40 * 419453 * 2
def baseEnd_419453 : Nat := 215381000970452621908477

theorem tailTrace_419453 : CollatzResearch.WordTrace tailWord_419453 prefixEnd_419453 215381000970452621908477 := by
  unfold tailWord_419453
  simp only [CollatzResearch.WordTrace]
  refine ⟨15298707749400892714207013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10199138499600595142804675 15298707749400892714207013)
  ·
    refine ⟨2868507703012667383913815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15298707749400892714207013 2868507703012667383913815)
    ·
      refine ⟨4302761554519001075870723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2868507703012667383913815 4302761554519001075870723)
      ·
        refine ⟨6454142331778501613806085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4302761554519001075870723 6454142331778501613806085)
        ·
          refine ⟨1210151687208469052588641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6454142331778501613806085 1210151687208469052588641)
          ·
            refine ⟨907613765406351789441481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1210151687208469052588641 907613765406351789441481)
            ·
              refine ⟨680710324054763842081111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 907613765406351789441481 680710324054763842081111)
              ·
                refine ⟨1021065486082145763121667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 680710324054763842081111 1021065486082145763121667)
                ·
                  refine ⟨1531598229123218644682501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1021065486082145763121667 1531598229123218644682501)
                  ·
                    refine ⟨287174667960603495877969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1531598229123218644682501 287174667960603495877969)
                    ·
                      refine ⟨215381000970452621908477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 287174667960603495877969 215381000970452621908477)
                      ·
                        rfl

theorem cell23_419453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 4, 2].length) (baseStart_419453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_419453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_419453 prefixEnd_419453 := by exact prefixLift 419453
  have htrace : WordTrace (prefixWord ++ tailWord_419453) baseStart_419453 baseEnd_419453 := by
    simpa [prefixWord, tailWord_419453, baseEnd_419453] using wordTrace_append hprefix tailTrace_419453
  have hstable : (prefixWord ++ tailWord_419453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419453).length < 2 ^ (prefixWord ++ tailWord_419453).sum := by decide
  have hdescent : baseEnd_419453 < baseStart_419453 := by decide
  rcases family_descends (prefixWord ++ tailWord_419453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419474 : List Nat := [3, 2, 3, 1, 4, 1, 2, 1, 1, 3, 2]
def baseStart_419474 : Nat := 118140960795 + 419474 * 2 ^ 59
def prefixEnd_419474 : Nat := 4983230072969 + 3 ^ 40 * 419474 * 2
def baseEnd_419474 : Nat := 215391784064197039745881

theorem tailTrace_419474 : CollatzResearch.WordTrace tailWord_419474 prefixEnd_419474 215391784064197039745881 := by
  unfold tailWord_419474
  simp only [CollatzResearch.WordTrace]
  refine ⟨3824868420581203325180369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10199649121549875533814317 3824868420581203325180369)
  ·
    refine ⟨2868651315435902493885277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3824868420581203325180369 2868651315435902493885277)
    ·
      refine ⟨1075744243288463435206979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2868651315435902493885277 1075744243288463435206979)
      ·
        refine ⟨1613616364932695152810469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1075744243288463435206979 1613616364932695152810469)
        ·
          refine ⟨302553068424880341151963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1613616364932695152810469 302553068424880341151963)
          ·
            refine ⟨453829602637320511727945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302553068424880341151963 453829602637320511727945)
            ·
              refine ⟨340372201977990383795959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 453829602637320511727945 340372201977990383795959)
              ·
                refine ⟨510558302966985575693939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 340372201977990383795959 510558302966985575693939)
                ·
                  refine ⟨765837454450478363540909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 510558302966985575693939 765837454450478363540909)
                  ·
                    refine ⟨287189045418929386327841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 765837454450478363540909 287189045418929386327841)
                    ·
                      refine ⟨215391784064197039745881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 287189045418929386327841 215391784064197039745881)
                      ·
                        rfl

theorem cell23_419474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_419474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_419474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_419474 prefixEnd_419474 := by exact prefixLift 419474
  have htrace : WordTrace (prefixWord ++ tailWord_419474) baseStart_419474 baseEnd_419474 := by
    simpa [prefixWord, tailWord_419474, baseEnd_419474] using wordTrace_append hprefix tailTrace_419474
  have hstable : (prefixWord ++ tailWord_419474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419474).length < 2 ^ (prefixWord ++ tailWord_419474).sum := by decide
  have hdescent : baseEnd_419474 < baseStart_419474 := by decide
  rcases family_descends (prefixWord ++ tailWord_419474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419546 : List Nat := [3, 1, 1, 2, 2, 3, 1, 1, 4, 2, 3]
def baseStart_419546 : Nat := 118140960795 + 419546 * 2 ^ 59
def prefixEnd_419546 : Nat := 4983230072969 + 3 ^ 40 * 419546 * 2
def baseEnd_419546 : Nat := 215428754671320758045549

theorem tailTrace_419546 : CollatzResearch.WordTrace tailWord_419546 prefixEnd_419546 215428754671320758045549 := by
  unfold tailWord_419546
  simp only [CollatzResearch.WordTrace]
  refine ⟨3825524934515992399335623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10201399825375979731561661 3825524934515992399335623)
  ·
    refine ⟨5738287401773988599003435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3825524934515992399335623 5738287401773988599003435)
    ·
      refine ⟨8607431102660982898505153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5738287401773988599003435 8607431102660982898505153)
      ·
        refine ⟨6455573326995737173878865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8607431102660982898505153 6455573326995737173878865)
        ·
          refine ⟨4841679995246802880409149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6455573326995737173878865 4841679995246802880409149)
          ·
            refine ⟨1815629998217551080153431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4841679995246802880409149 1815629998217551080153431)
            ·
              refine ⟨2723444997326326620230147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1815629998217551080153431 2723444997326326620230147)
              ·
                refine ⟨4085167495989489930345221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2723444997326326620230147 4085167495989489930345221)
                ·
                  refine ⟨765968905498029361939729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4085167495989489930345221 765968905498029361939729)
                  ·
                    refine ⟨574476679123522021454797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 765968905498029361939729 574476679123522021454797)
                    ·
                      refine ⟨215428754671320758045549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 574476679123522021454797 215428754671320758045549)
                      ·
                        rfl

theorem cell23_419546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 4, 2, 3].length) (baseStart_419546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_419546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_419546 prefixEnd_419546 := by exact prefixLift 419546
  have htrace : WordTrace (prefixWord ++ tailWord_419546) baseStart_419546 baseEnd_419546 := by
    simpa [prefixWord, tailWord_419546, baseEnd_419546] using wordTrace_append hprefix tailTrace_419546
  have hstable : (prefixWord ++ tailWord_419546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419546).length < 2 ^ (prefixWord ++ tailWord_419546).sum := by decide
  have hdescent : baseEnd_419546 < baseStart_419546 := by decide
  rcases family_descends (prefixWord ++ tailWord_419546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419566 : List Nat := [4, 1, 2, 1, 1, 2, 3, 3, 6]
def baseStart_419566 : Nat := 118140960795 + 419566 * 2 ^ 59
def prefixEnd_419566 : Nat := 4983230072969 + 3 ^ 40 * 419566 * 2
def baseEnd_419566 : Nat := 23937669364934519977273

theorem tailTrace_419566 : CollatzResearch.WordTrace tailWord_419566 prefixEnd_419566 23937669364934519977273 := by
  unfold tailWord_419566
  simp only [CollatzResearch.WordTrace]
  refine ⟨1912853649748939126633819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10201886131994342008713701 1912853649748939126633819)
  ·
    refine ⟨2869280474623408689950729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1912853649748939126633819 2869280474623408689950729)
    ·
      refine ⟨2151960355967556517463047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2869280474623408689950729 2151960355967556517463047)
      ·
        refine ⟨3227940533951334776194571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2151960355967556517463047 3227940533951334776194571)
        ·
          refine ⟨4841910800927002164291857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3227940533951334776194571 4841910800927002164291857)
          ·
            refine ⟨3631433100695251623218893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4841910800927002164291857 3631433100695251623218893)
            ·
              refine ⟨1361787412760719358707085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3631433100695251623218893 1361787412760719358707085)
              ·
                refine ⟨510670279785269759515157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1361787412760719358707085 510670279785269759515157)
                ·
                  refine ⟨23937669364934519977273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 510670279785269759515157 23937669364934519977273)
                  ·
                    rfl

theorem cell23_419566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 6].length) (baseStart_419566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_419566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_419566 prefixEnd_419566 := by exact prefixLift 419566
  have htrace : WordTrace (prefixWord ++ tailWord_419566) baseStart_419566 baseEnd_419566 := by
    simpa [prefixWord, tailWord_419566, baseEnd_419566] using wordTrace_append hprefix tailTrace_419566
  have hstable : (prefixWord ++ tailWord_419566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419566).length < 2 ^ (prefixWord ++ tailWord_419566).sum := by decide
  have hdescent : baseEnd_419566 < baseStart_419566 := by decide
  rcases family_descends (prefixWord ++ tailWord_419566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419596 : List Nat := [2, 2, 1, 2, 2, 1, 2, 5, 1, 5]
def baseStart_419596 : Nat := 118140960795 + 419596 * 2 ^ 59
def prefixEnd_419596 : Nat := 4983230072969 + 3 ^ 40 * 419596 * 2
def baseEnd_419596 : Nat := 71818142901348520806773

theorem tailTrace_419596 : CollatzResearch.WordTrace tailWord_419596 prefixEnd_419596 71818142901348520806773 := by
  unfold tailWord_419596
  simp only [CollatzResearch.WordTrace]
  refine ⟨7651961693941414068331321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10202615591921885424441761 7651961693941414068331321)
  ·
    refine ⟨5738971270456060551248491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7651961693941414068331321 5738971270456060551248491)
    ·
      refine ⟨8608456905684090826872737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5738971270456060551248491 8608456905684090826872737)
      ·
        refine ⟨6456342679263068120154553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8608456905684090826872737 6456342679263068120154553)
        ·
          refine ⟨4842257009447301090115915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6456342679263068120154553 4842257009447301090115915)
          ·
            refine ⟨7263385514170951635173873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4842257009447301090115915 7263385514170951635173873)
            ·
              refine ⟨5447539135628213726380405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7263385514170951635173873 5447539135628213726380405)
              ·
                refine ⟨510706793965145036848163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5447539135628213726380405 510706793965145036848163)
                ·
                  refine ⟨766060190947717555272245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 510706793965145036848163 766060190947717555272245)
                  ·
                    refine ⟨71818142901348520806773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 766060190947717555272245 71818142901348520806773)
                    ·
                      rfl

theorem cell23_419596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 1, 5].length) (baseStart_419596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_419596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_419596 prefixEnd_419596 := by exact prefixLift 419596
  have htrace : WordTrace (prefixWord ++ tailWord_419596) baseStart_419596 baseEnd_419596 := by
    simpa [prefixWord, tailWord_419596, baseEnd_419596] using wordTrace_append hprefix tailTrace_419596
  have hstable : (prefixWord ++ tailWord_419596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419596).length < 2 ^ (prefixWord ++ tailWord_419596).sum := by decide
  have hdescent : baseEnd_419596 < baseStart_419596 := by decide
  rcases family_descends (prefixWord ++ tailWord_419596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419616 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 4]
def baseStart_419616 : Nat := 118140960795 + 419616 * 2 ^ 59
def prefixEnd_419616 : Nat := 4983230072969 + 3 ^ 40 * 419616 * 2
def baseEnd_419616 : Nat := 215464698317135484170227

theorem tailTrace_419616 : CollatzResearch.WordTrace tailWord_419616 prefixEnd_419616 215464698317135484170227 := by
  unfold tailWord_419616
  simp only [CollatzResearch.WordTrace]
  refine ⟨7652326423905185776195351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10203101898540247701593801 7652326423905185776195351)
  ·
    refine ⟨11478489635857778664293027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7652326423905185776195351 11478489635857778664293027)
    ·
      refine ⟨17217734453786667996439541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11478489635857778664293027 17217734453786667996439541)
      ·
        refine ⟨1614162605042500124666207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17217734453786667996439541 1614162605042500124666207)
        ·
          refine ⟨2421243907563750186999311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1614162605042500124666207 2421243907563750186999311)
          ·
            refine ⟨3631865861345625280498967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2421243907563750186999311 3631865861345625280498967)
            ·
              refine ⟨5447798792018437920748451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3631865861345625280498967 5447798792018437920748451)
              ·
                refine ⟨8171698188027656881122677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5447798792018437920748451 8171698188027656881122677)
                ·
                  refine ⟨766096705127592832605251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8171698188027656881122677 766096705127592832605251)
                  ·
                    refine ⟨1149145057691389248907877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 766096705127592832605251 1149145057691389248907877)
                    ·
                      refine ⟨215464698317135484170227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1149145057691389248907877 215464698317135484170227)
                      ·
                        rfl

theorem cell23_419616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_419616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_419616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_419616 prefixEnd_419616 := by exact prefixLift 419616
  have htrace : WordTrace (prefixWord ++ tailWord_419616) baseStart_419616 baseEnd_419616 := by
    simpa [prefixWord, tailWord_419616, baseEnd_419616] using wordTrace_append hprefix tailTrace_419616
  have hstable : (prefixWord ++ tailWord_419616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419616).length < 2 ^ (prefixWord ++ tailWord_419616).sum := by decide
  have hdescent : baseEnd_419616 < baseStart_419616 := by decide
  rcases family_descends (prefixWord ++ tailWord_419616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419637 : List Nat := [1, 3, 3, 1, 4, 2, 1, 1, 2, 3, 2]
def baseStart_419637 : Nat := 118140960795 + 419637 * 2 ^ 59
def prefixEnd_419637 : Nat := 4983230072969 + 3 ^ 40 * 419637 * 2
def baseEnd_419637 : Nat := 215475481410879902007631

theorem tailTrace_419637 : CollatzResearch.WordTrace tailWord_419637 prefixEnd_419637 215475481410879902007631 := by
  unfold tailWord_419637
  simp only [CollatzResearch.WordTrace]
  refine ⟨15305418780734292138905165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10203612520489528092603443 15305418780734292138905165)
  ·
    refine ⟨5739532042775359552089437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15305418780734292138905165 5739532042775359552089437)
    ·
      refine ⟨2152324516040759832033539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5739532042775359552089437 2152324516040759832033539)
      ·
        refine ⟨3228486774061139748050309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2152324516040759832033539 3228486774061139748050309)
        ·
          refine ⟨605341270136463702759433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3228486774061139748050309 605341270136463702759433)
          ·
            refine ⟨454005952602347777069575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 605341270136463702759433 454005952602347777069575)
            ·
              refine ⟨681008928903521665604363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 454005952602347777069575 681008928903521665604363)
              ·
                refine ⟨1021513393355282498406545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 681008928903521665604363 1021513393355282498406545)
                ·
                  refine ⟨766135045016461873804909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1021513393355282498406545 766135045016461873804909)
                  ·
                    refine ⟨287300641881173202676841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 766135045016461873804909 287300641881173202676841)
                    ·
                      refine ⟨215475481410879902007631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 287300641881173202676841 215475481410879902007631)
                      ·
                        rfl

theorem cell23_419637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_419637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_419637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_419637 prefixEnd_419637 := by exact prefixLift 419637
  have htrace : WordTrace (prefixWord ++ tailWord_419637) baseStart_419637 baseEnd_419637 := by
    simpa [prefixWord, tailWord_419637, baseEnd_419637] using wordTrace_append hprefix tailTrace_419637
  have hstable : (prefixWord ++ tailWord_419637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419637).length < 2 ^ (prefixWord ++ tailWord_419637).sum := by decide
  have hdescent : baseEnd_419637 < baseStart_419637 := by decide
  rcases family_descends (prefixWord ++ tailWord_419637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419647 : List Nat := [1, 1, 2, 2, 7, 1, 2, 1, 1, 5]
def baseStart_419647 : Nat := 118140960795 + 419647 * 2 ^ 59
def prefixEnd_419647 : Nat := 4983230072969 + 3 ^ 40 * 419647 * 2
def baseEnd_419647 : Nat := 71826872072474954294195

theorem tailTrace_419647 : CollatzResearch.WordTrace tailWord_419647 prefixEnd_419647 71826872072474954294195 := by
  unfold tailWord_419647
  simp only [CollatzResearch.WordTrace]
  refine ⟨15305783510698063846769195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10203855673798709231179463 15305783510698063846769195)
  ·
    refine ⟨22958675266047095770153793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15305783510698063846769195 22958675266047095770153793)
    ·
      refine ⟨17219006449535321827615345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22958675266047095770153793 17219006449535321827615345)
      ·
        refine ⟨12914254837151491370711509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17219006449535321827615345 12914254837151491370711509)
        ·
          refine ⟨302677847745738079001051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 12914254837151491370711509 302677847745738079001051)
          ·
            refine ⟨454016771618607118501577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302677847745738079001051 454016771618607118501577)
            ·
              refine ⟨340512578713955338876183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 454016771618607118501577 340512578713955338876183)
              ·
                refine ⟨510768868070933008314275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 340512578713955338876183 510768868070933008314275)
                ·
                  refine ⟨766153302106399512471413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 510768868070933008314275 766153302106399512471413)
                  ·
                    refine ⟨71826872072474954294195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 766153302106399512471413 71826872072474954294195)
                    ·
                      rfl

theorem cell23_419647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 1, 5].length) (baseStart_419647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_419647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_419647 prefixEnd_419647 := by exact prefixLift 419647
  have htrace : WordTrace (prefixWord ++ tailWord_419647) baseStart_419647 baseEnd_419647 := by
    simpa [prefixWord, tailWord_419647, baseEnd_419647] using wordTrace_append hprefix tailTrace_419647
  have hstable : (prefixWord ++ tailWord_419647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419647).length < 2 ^ (prefixWord ++ tailWord_419647).sum := by decide
  have hdescent : baseEnd_419647 < baseStart_419647 := by decide
  rcases family_descends (prefixWord ++ tailWord_419647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419653 : List Nat := [1, 3, 1, 1, 1, 2, 5, 3, 1, 2, 3]
def baseStart_419653 : Nat := 118140960795 + 419653 * 2 ^ 59
def prefixEnd_419653 : Nat := 4983230072969 + 3 ^ 40 * 419653 * 2
def baseEnd_419653 : Nat := 215483697101351839407557

theorem tailTrace_419653 : CollatzResearch.WordTrace tailWord_419653 prefixEnd_419653 215483697101351839407557 := by
  unfold tailWord_419653
  simp only [CollatzResearch.WordTrace]
  refine ⟨15306002348676326871487613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10204001565784217914325075 15306002348676326871487613)
  ·
    refine ⟨5739750880753622576807855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15306002348676326871487613 5739750880753622576807855)
    ·
      refine ⟨8609626321130433865211783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5739750880753622576807855 8609626321130433865211783)
      ·
        refine ⟨12914439481695650797817675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8609626321130433865211783 12914439481695650797817675)
        ·
          refine ⟨19371659222543476196726513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12914439481695650797817675 19371659222543476196726513)
          ·
            refine ⟨14528744416907607147544885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19371659222543476196726513 14528744416907607147544885)
            ·
              refine ⟨1362069789085088170082333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14528744416907607147544885 1362069789085088170082333)
              ·
                refine ⟨510776170906908063780875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1362069789085088170082333 510776170906908063780875)
                ·
                  refine ⟨766164256360362095671313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 510776170906908063780875 766164256360362095671313)
                  ·
                    refine ⟨574623192270271571753485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 766164256360362095671313 574623192270271571753485)
                    ·
                      refine ⟨215483697101351839407557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 574623192270271571753485 215483697101351839407557)
                      ·
                        rfl

theorem cell23_419653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 2, 3].length) (baseStart_419653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_419653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_419653 prefixEnd_419653 := by exact prefixLift 419653
  have htrace : WordTrace (prefixWord ++ tailWord_419653) baseStart_419653 baseEnd_419653 := by
    simpa [prefixWord, tailWord_419653, baseEnd_419653] using wordTrace_append hprefix tailTrace_419653
  have hstable : (prefixWord ++ tailWord_419653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419653).length < 2 ^ (prefixWord ++ tailWord_419653).sum := by decide
  have hdescent : baseEnd_419653 < baseStart_419653 := by decide
  rcases family_descends (prefixWord ++ tailWord_419653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419716 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 4, 6]
def baseStart_419716 : Nat := 118140960795 + 419716 * 2 ^ 59
def prefixEnd_419716 : Nat := 4983230072969 + 3 ^ 40 * 419716 * 2
def baseEnd_419716 : Nat := 71838682127528364306589

theorem tailTrace_419716 : CollatzResearch.WordTrace tailWord_419716 prefixEnd_419716 71838682127528364306589 := by
  unfold tailWord_419716
  simp only [CollatzResearch.WordTrace]
  refine ⟨7654150073724044315515501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10205533431632059087354001 7654150073724044315515501)
  ·
    refine ⟨2870306277646516618318313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7654150073724044315515501 2870306277646516618318313)
    ·
      refine ⟨2152729708234887463738735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2870306277646516618318313 2152729708234887463738735)
      ·
        refine ⟨3229094562352331195608103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2152729708234887463738735 3229094562352331195608103)
        ·
          refine ⟨4843641843528496793412155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3229094562352331195608103 4843641843528496793412155)
          ·
            refine ⟨7265462765292745190118233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4843641843528496793412155 7265462765292745190118233)
            ·
              refine ⟨5449097073969558892588675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7265462765292745190118233 5449097073969558892588675)
              ·
                refine ⟨8173645610954338338883013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5449097073969558892588675 8173645610954338338883013)
                ·
                  refine ⟨1532558552053938438540565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8173645610954338338883013 1532558552053938438540565)
                  ·
                    refine ⟨71838682127528364306589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1532558552053938438540565 71838682127528364306589)
                    ·
                      rfl

theorem cell23_419716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_419716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_419716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_419716 prefixEnd_419716 := by exact prefixLift 419716
  have htrace : WordTrace (prefixWord ++ tailWord_419716) baseStart_419716 baseEnd_419716 := by
    simpa [prefixWord, tailWord_419716, baseEnd_419716] using wordTrace_append hprefix tailTrace_419716
  have hstable : (prefixWord ++ tailWord_419716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419716).length < 2 ^ (prefixWord ++ tailWord_419716).sum := by decide
  have hdescent : baseEnd_419716 < baseStart_419716 := by decide
  rcases family_descends (prefixWord ++ tailWord_419716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419763 : List Nat := [1, 1, 1, 2, 3, 1, 4, 5, 5]
def baseStart_419763 : Nat := 118140960795 + 419763 * 2 ^ 59
def prefixEnd_419763 : Nat := 4983230072969 + 3 ^ 40 * 419763 * 2
def baseEnd_419763 : Nat := 23948908885927378781339

theorem tailTrace_419763 : CollatzResearch.WordTrace tailWord_419763 prefixEnd_419763 23948908885927378781339 := by
  unfold tailWord_419763
  simp only [CollatzResearch.WordTrace]
  refine ⟨15310014378277815657991943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10206676252185210438661295 15310014378277815657991943)
  ·
    refine ⟨22965021567416723486987915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15310014378277815657991943 22965021567416723486987915)
    ·
      refine ⟨34447532351125085230481873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22965021567416723486987915 34447532351125085230481873)
      ·
        refine ⟨25835649263343813922861405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34447532351125085230481873 25835649263343813922861405)
        ·
          refine ⟨9688368473753930221073027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25835649263343813922861405 9688368473753930221073027)
          ·
            refine ⟨14532552710630895331609541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9688368473753930221073027 14532552710630895331609541)
            ·
              refine ⟨2724853633243292874676789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14532552710630895331609541 2724853633243292874676789)
              ·
                refine ⟨255455028116558707000949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2724853633243292874676789 255455028116558707000949)
                ·
                  refine ⟨23948908885927378781339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 255455028116558707000949 23948908885927378781339)
                  ·
                    rfl

theorem cell23_419763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 5, 5].length) (baseStart_419763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_419763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_419763 prefixEnd_419763 := by exact prefixLift 419763
  have htrace : WordTrace (prefixWord ++ tailWord_419763) baseStart_419763 baseEnd_419763 := by
    simpa [prefixWord, tailWord_419763, baseEnd_419763] using wordTrace_append hprefix tailTrace_419763
  have hstable : (prefixWord ++ tailWord_419763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419763).length < 2 ^ (prefixWord ++ tailWord_419763).sum := by decide
  have hdescent : baseEnd_419763 < baseStart_419763 := by decide
  rcases family_descends (prefixWord ++ tailWord_419763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419774 : List Nat := [4, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2]
def baseStart_419774 : Nat := 118140960795 + 419774 * 2 ^ 59
def prefixEnd_419774 : Nat := 4983230072969 + 3 ^ 40 * 419774 * 2
def baseEnd_419774 : Nat := 215545828260545865994501

theorem tailTrace_419774 : CollatzResearch.WordTrace tailWord_419774 prefixEnd_419774 215545828260545865994501 := by
  unfold tailWord_419774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1913801947654745567080297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10206943720825309691094917 1913801947654745567080297)
  ·
    refine ⟨1435351460741059175310223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1913801947654745567080297 1435351460741059175310223)
    ·
      refine ⟨2153027191111588762965335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1435351460741059175310223 2153027191111588762965335)
      ·
        refine ⟨3229540786667383144448003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2153027191111588762965335 3229540786667383144448003)
        ·
          refine ⟨4844311180001074716672005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3229540786667383144448003 4844311180001074716672005)
          ·
            refine ⟨908308346250201509376001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4844311180001074716672005 908308346250201509376001)
            ·
              refine ⟨681231259687651132032001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 908308346250201509376001 681231259687651132032001)
              ·
                refine ⟨510923444765738349024001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 681231259687651132032001 510923444765738349024001)
                ·
                  refine ⟨383192583574303761768001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 510923444765738349024001 383192583574303761768001)
                  ·
                    refine ⟨287394437680727821326001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 383192583574303761768001 287394437680727821326001)
                    ·
                      refine ⟨215545828260545865994501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 287394437680727821326001 215545828260545865994501)
                      ·
                        rfl

theorem cell23_419774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_419774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_419774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_419774 prefixEnd_419774 := by exact prefixLift 419774
  have htrace : WordTrace (prefixWord ++ tailWord_419774) baseStart_419774 baseEnd_419774 := by
    simpa [prefixWord, tailWord_419774, baseEnd_419774] using wordTrace_append hprefix tailTrace_419774
  have hstable : (prefixWord ++ tailWord_419774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419774).length < 2 ^ (prefixWord ++ tailWord_419774).sum := by decide
  have hdescent : baseEnd_419774 < baseStart_419774 := by decide
  rcases family_descends (prefixWord ++ tailWord_419774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419823 : List Nat := [1, 1, 2, 1, 4, 2, 1, 2, 5, 4]
def baseStart_419823 : Nat := 118140960795 + 419823 * 2 ^ 59
def prefixEnd_419823 : Nat := 4983230072969 + 3 ^ 40 * 419823 * 2
def baseEnd_419823 : Nat := 71856996270872058093925

theorem tailTrace_419823 : CollatzResearch.WordTrace tailWord_419823 prefixEnd_419823 71856996270872058093925 := by
  unfold tailWord_419823
  simp only [CollatzResearch.WordTrace]
  refine ⟨15312202758060445905176123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10208135172040297270117415 15312202758060445905176123)
  ·
    refine ⟨22968304137090668857764185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15312202758060445905176123 22968304137090668857764185)
    ·
      refine ⟨17226228102818001643323139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22968304137090668857764185 17226228102818001643323139)
      ·
        refine ⟨25839342154227002464984709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17226228102818001643323139 25839342154227002464984709)
        ·
          refine ⟨4844876653917562962184633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25839342154227002464984709 4844876653917562962184633)
          ·
            refine ⟨3633657490438172221638475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4844876653917562962184633 3633657490438172221638475)
            ·
              refine ⟨5450486235657258332457713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3633657490438172221638475 5450486235657258332457713)
              ·
                refine ⟨4087864676742943749343285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5450486235657258332457713 4087864676742943749343285)
                ·
                  refine ⟨383237313444650976500933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4087864676742943749343285 383237313444650976500933)
                  ·
                    refine ⟨71856996270872058093925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 383237313444650976500933 71856996270872058093925)
                    ·
                      rfl

theorem cell23_419823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 5, 4].length) (baseStart_419823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_419823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_419823 prefixEnd_419823 := by exact prefixLift 419823
  have htrace : WordTrace (prefixWord ++ tailWord_419823) baseStart_419823 baseEnd_419823 := by
    simpa [prefixWord, tailWord_419823, baseEnd_419823] using wordTrace_append hprefix tailTrace_419823
  have hstable : (prefixWord ++ tailWord_419823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419823).length < 2 ^ (prefixWord ++ tailWord_419823).sum := by decide
  have hdescent : baseEnd_419823 < baseStart_419823 := by decide
  rcases family_descends (prefixWord ++ tailWord_419823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419913 : List Nat := [1, 2, 1, 1, 2, 2, 4, 3, 1, 6]
def baseStart_419913 : Nat := 118140960795 + 419913 * 2 ^ 59
def prefixEnd_419913 : Nat := 4983230072969 + 3 ^ 40 * 419913 * 2
def baseEnd_419913 : Nat := 71872400690506940718787

theorem tailTrace_419913 : CollatzResearch.WordTrace tailWord_419913 prefixEnd_419913 71872400690506940718787 := by
  unfold tailWord_419913
  simp only [CollatzResearch.WordTrace]
  refine ⟨15315485327734391275952393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10210323551822927517301595 15315485327734391275952393)
  ·
    refine ⟨11486613995800793456964295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15315485327734391275952393 11486613995800793456964295)
    ·
      refine ⟨17229920993701190185446443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11486613995800793456964295 17229920993701190185446443)
      ·
        refine ⟨25844881490551785278169665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17229920993701190185446443 25844881490551785278169665)
        ·
          refine ⟨19383661117913838958627249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25844881490551785278169665 19383661117913838958627249)
          ·
            refine ⟨14537745838435379218970437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19383661117913838958627249 14537745838435379218970437)
            ·
              refine ⟨2725827344706633603556957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14537745838435379218970437 2725827344706633603556957)
              ·
                refine ⟨1022185254264987601333859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2725827344706633603556957 1022185254264987601333859)
                ·
                  refine ⟨1533277881397481402000789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1022185254264987601333859 1533277881397481402000789)
                  ·
                    refine ⟨71872400690506940718787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1533277881397481402000789 71872400690506940718787)
                    ·
                      rfl

theorem cell23_419913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 6].length) (baseStart_419913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_419913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_419913 prefixEnd_419913 := by exact prefixLift 419913
  have htrace : WordTrace (prefixWord ++ tailWord_419913) baseStart_419913 baseEnd_419913 := by
    simpa [prefixWord, tailWord_419913, baseEnd_419913] using wordTrace_append hprefix tailTrace_419913
  have hstable : (prefixWord ++ tailWord_419913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419913).length < 2 ^ (prefixWord ++ tailWord_419913).sum := by decide
  have hdescent : baseEnd_419913 < baseStart_419913 := by decide
  rcases family_descends (prefixWord ++ tailWord_419913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419940 : List Nat := [2, 3, 1, 1, 2, 1, 5, 1, 1, 1, 5]
def baseStart_419940 : Nat := 118140960795 + 419940 * 2 ^ 59
def prefixEnd_419940 : Nat := 4983230072969 + 3 ^ 40 * 419940 * 2
def baseEnd_419940 : Nat := 215631066049192216518737

theorem tailTrace_419940 : CollatzResearch.WordTrace tailWord_419940 prefixEnd_419940 215631066049192216518737 := by
  unfold tailWord_419940
  simp only [CollatzResearch.WordTrace]
  refine ⟨7658235049318287443592637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10210980065757716591456849 7658235049318287443592637)
  ·
    refine ⟨2871838143494357791347239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7658235049318287443592637 2871838143494357791347239)
    ·
      refine ⟨4307757215241536687020859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2871838143494357791347239 4307757215241536687020859)
      ·
        refine ⟨6461635822862305030531289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4307757215241536687020859 6461635822862305030531289)
        ·
          refine ⟨4846226867146728772898467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6461635822862305030531289 4846226867146728772898467)
          ·
            refine ⟨7269340300720093159347701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4846226867146728772898467 7269340300720093159347701)
            ·
              refine ⟨681500653192508733688847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7269340300720093159347701 681500653192508733688847)
              ·
                refine ⟨1022250979788763100533271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 681500653192508733688847 1022250979788763100533271)
                ·
                  refine ⟨1533376469683144650799907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1022250979788763100533271 1533376469683144650799907)
                  ·
                    refine ⟨2300064704524716976199861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1533376469683144650799907 2300064704524716976199861)
                    ·
                      refine ⟨215631066049192216518737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2300064704524716976199861 215631066049192216518737)
                      ·
                        rfl

theorem cell23_419940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 1, 1, 5].length) (baseStart_419940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_419940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_419940 prefixEnd_419940 := by exact prefixLift 419940
  have htrace : WordTrace (prefixWord ++ tailWord_419940) baseStart_419940 baseEnd_419940 := by
    simpa [prefixWord, tailWord_419940, baseEnd_419940] using wordTrace_append hprefix tailTrace_419940
  have hstable : (prefixWord ++ tailWord_419940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419940).length < 2 ^ (prefixWord ++ tailWord_419940).sum := by decide
  have hdescent : baseEnd_419940 < baseStart_419940 := by decide
  rcases family_descends (prefixWord ++ tailWord_419940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419950 : List Nat := [4, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4]
def baseStart_419950 : Nat := 118140960795 + 419950 * 2 ^ 59
def prefixEnd_419950 : Nat := 4983230072969 + 3 ^ 40 * 419950 * 2
def baseEnd_419950 : Nat := 215636200855737177393691

theorem tailTrace_419950 : CollatzResearch.WordTrace tailWord_419950 prefixEnd_419950 215636200855737177393691 := by
  unfold tailWord_419950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1914604353575043324381163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10211223219066897730032869 1914604353575043324381163)
  ·
    refine ⟨2871906530362564986571745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1914604353575043324381163 2871906530362564986571745)
    ·
      refine ⟨2153929897771923739928809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2871906530362564986571745 2153929897771923739928809)
      ·
        refine ⟨1615447423328942804946607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2153929897771923739928809 1615447423328942804946607)
        ·
          refine ⟨2423171134993414207419911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1615447423328942804946607 2423171134993414207419911)
          ·
            refine ⟨3634756702490121311129867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2423171134993414207419911 3634756702490121311129867)
            ·
              refine ⟨5452135053735181966694801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3634756702490121311129867 5452135053735181966694801)
              ·
                refine ⟨4089101290301386475021101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5452135053735181966694801 4089101290301386475021101)
                ·
                  refine ⟨1533412983863019928132913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4089101290301386475021101 1533412983863019928132913)
                  ·
                    refine ⟨1150059737897264946099685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1533412983863019928132913 1150059737897264946099685)
                    ·
                      refine ⟨215636200855737177393691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1150059737897264946099685 215636200855737177393691)
                      ·
                        rfl

theorem cell23_419950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_419950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_419950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_419950 prefixEnd_419950 := by exact prefixLift 419950
  have htrace : WordTrace (prefixWord ++ tailWord_419950) baseStart_419950 baseEnd_419950 := by
    simpa [prefixWord, tailWord_419950, baseEnd_419950] using wordTrace_append hprefix tailTrace_419950
  have hstable : (prefixWord ++ tailWord_419950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419950).length < 2 ^ (prefixWord ++ tailWord_419950).sum := by decide
  have hdescent : baseEnd_419950 < baseStart_419950 := by decide
  rcases family_descends (prefixWord ++ tailWord_419950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419988 : List Nat := [2, 4, 2, 3, 1, 2, 2, 1, 1, 1, 4]
def baseStart_419988 : Nat := 118140960795 + 419988 * 2 ^ 59
def prefixEnd_419988 : Nat := 4983230072969 + 3 ^ 40 * 419988 * 2
def baseEnd_419988 : Nat := 215655713120608028718517

theorem tailTrace_419988 : CollatzResearch.WordTrace tailWord_419988 prefixEnd_419988 215655713120608028718517 := by
  unfold tailWord_419988
  simp only [CollatzResearch.WordTrace]
  refine ⟨7659110401231339542466309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10212147201641786056621745 7659110401231339542466309)
  ·
    refine ⟨1436083200230876164212433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7659110401231339542466309 1436083200230876164212433)
    ·
      refine ⟨1077062400173157123159325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1436083200230876164212433 1077062400173157123159325)
      ·
        refine ⟨403898400064933921184747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1077062400173157123159325 403898400064933921184747)
        ·
          refine ⟨605847600097400881777121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403898400064933921184747 605847600097400881777121)
          ·
            refine ⟨454385700073050661332841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 605847600097400881777121 454385700073050661332841)
            ·
              refine ⟨340789275054787995999631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 454385700073050661332841 340789275054787995999631)
              ·
                refine ⟨511183912582181993999447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 340789275054787995999631 511183912582181993999447)
                ·
                  refine ⟨766775868873272990999171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 511183912582181993999447 766775868873272990999171)
                  ·
                    refine ⟨1150163803309909486498757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 766775868873272990999171 1150163803309909486498757)
                    ·
                      refine ⟨215655713120608028718517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1150163803309909486498757 215655713120608028718517)
                      ·
                        rfl

theorem cell23_419988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_419988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_419988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_419988 prefixEnd_419988 := by exact prefixLift 419988
  have htrace : WordTrace (prefixWord ++ tailWord_419988) baseStart_419988 baseEnd_419988 := by
    simpa [prefixWord, tailWord_419988, baseEnd_419988] using wordTrace_append hprefix tailTrace_419988
  have hstable : (prefixWord ++ tailWord_419988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419988).length < 2 ^ (prefixWord ++ tailWord_419988).sum := by decide
  have hdescent : baseEnd_419988 < baseStart_419988 := by decide
  rcases family_descends (prefixWord ++ tailWord_419988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419991 : List Nat := [1, 1, 3, 3, 4, 2, 2, 1, 1, 2, 3]
def baseStart_419991 : Nat := 118140960795 + 419991 * 2 ^ 59
def prefixEnd_419991 : Nat := 4983230072969 + 3 ^ 40 * 419991 * 2
def baseEnd_419991 : Nat := 215657253562571516981003

theorem tailTrace_419991 : CollatzResearch.WordTrace tailWord_419991 prefixEnd_419991 215657253562571516981003 := by
  unfold tailWord_419991
  simp only [CollatzResearch.WordTrace]
  refine ⟨15318330221451810597291827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10212220147634540398194551 15318330221451810597291827)
  ·
    refine ⟨22977495332177715895937741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15318330221451810597291827 22977495332177715895937741)
    ·
      refine ⟨8616560749566643460976653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22977495332177715895937741 8616560749566643460976653)
      ·
        refine ⟨3231210281087491297866245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8616560749566643460976653 3231210281087491297866245)
        ·
          refine ⟨605851927703904618349921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3231210281087491297866245 605851927703904618349921)
          ·
            refine ⟨454388945777928463762441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 605851927703904618349921 454388945777928463762441)
            ·
              refine ⟨340791709333446347821831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 454388945777928463762441 340791709333446347821831)
              ·
                refine ⟨511187564000169521732747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 340791709333446347821831 511187564000169521732747)
                ·
                  refine ⟨766781346000254282599121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 511187564000169521732747 766781346000254282599121)
                  ·
                    refine ⟨575086009500190711949341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 766781346000254282599121 575086009500190711949341)
                    ·
                      refine ⟨215657253562571516981003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 575086009500190711949341 215657253562571516981003)
                      ·
                        rfl

theorem cell23_419991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_419991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_419991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_419991 prefixEnd_419991 := by exact prefixLift 419991
  have htrace : WordTrace (prefixWord ++ tailWord_419991) baseStart_419991 baseEnd_419991 := by
    simpa [prefixWord, tailWord_419991, baseEnd_419991] using wordTrace_append hprefix tailTrace_419991
  have hstable : (prefixWord ++ tailWord_419991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419991).length < 2 ^ (prefixWord ++ tailWord_419991).sum := by decide
  have hdescent : baseEnd_419991 < baseStart_419991 := by decide
  rcases family_descends (prefixWord ++ tailWord_419991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419998 : List Nat := [4, 3, 1, 1, 4, 1, 1, 2, 2, 4]
def baseStart_419998 : Nat := 118140960795 + 419998 * 2 ^ 59
def prefixEnd_419998 : Nat := 4983230072969 + 3 ^ 40 * 419998 * 2
def baseEnd_419998 : Nat := 71886949309050996531157

theorem tailTrace_419998 : CollatzResearch.WordTrace tailWord_419998 prefixEnd_419998 71886949309050996531157 := by
  unfold tailWord_419998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1914823191553306349099581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10212390354950967195197765 1914823191553306349099581)
  ·
    refine ⟨718058696832489880912343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1914823191553306349099581 718058696832489880912343)
    ·
      refine ⟨1077088045248734821368515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 718058696832489880912343 1077088045248734821368515)
      ·
        refine ⟨1615632067873102232052773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1077088045248734821368515 1615632067873102232052773)
        ·
          refine ⟨302931012726206668509895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1615632067873102232052773 302931012726206668509895)
          ·
            refine ⟨454396519089310002764843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302931012726206668509895 454396519089310002764843)
            ·
              refine ⟨681594778633965004147265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 454396519089310002764843 681594778633965004147265)
              ·
                refine ⟨511196083975473753110449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 681594778633965004147265 511196083975473753110449)
                ·
                  refine ⟨383397062981605314832837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 511196083975473753110449 383397062981605314832837)
                  ·
                    refine ⟨71886949309050996531157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 383397062981605314832837 71886949309050996531157)
                    ·
                      rfl

theorem cell23_419998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_419998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_419998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_419998 prefixEnd_419998 := by exact prefixLift 419998
  have htrace : WordTrace (prefixWord ++ tailWord_419998) baseStart_419998 baseEnd_419998 := by
    simpa [prefixWord, tailWord_419998, baseEnd_419998] using wordTrace_append hprefix tailTrace_419998
  have hstable : (prefixWord ++ tailWord_419998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419998).length < 2 ^ (prefixWord ++ tailWord_419998).sum := by decide
  have hdescent : baseEnd_419998 < baseStart_419998 := by decide
  rcases family_descends (prefixWord ++ tailWord_419998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420004 : List Nat := [2, 3, 1, 2, 4, 1, 1, 1, 4, 1, 3]
def baseStart_420004 : Nat := 118140960795 + 420004 * 2 ^ 59
def prefixEnd_420004 : Nat := 4983230072969 + 3 ^ 40 * 420004 * 2
def baseEnd_420004 : Nat := 215663928811079966118443

theorem tailTrace_420004 : CollatzResearch.WordTrace tailWord_420004 prefixEnd_420004 215663928811079966118443 := by
  unfold tailWord_420004
  simp only [CollatzResearch.WordTrace]
  refine ⟨7659402185202356908757533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10212536246936475878343377 7659402185202356908757533)
  ·
    refine ⟨2872275819450883840784075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7659402185202356908757533 2872275819450883840784075)
    ·
      refine ⟨4308413729176325761176113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2872275819450883840784075 4308413729176325761176113)
      ·
        refine ⟨3231310296882244320882085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4308413729176325761176113 3231310296882244320882085)
        ·
          refine ⟨605870680665420810165391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3231310296882244320882085 605870680665420810165391)
          ·
            refine ⟨908806020998131215248087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 605870680665420810165391 908806020998131215248087)
            ·
              refine ⟨1363209031497196822872131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 908806020998131215248087 1363209031497196822872131)
              ·
                refine ⟨2044813547245795234308197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1363209031497196822872131 2044813547245795234308197)
                ·
                  refine ⟨383402540108586606432787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2044813547245795234308197 383402540108586606432787)
                  ·
                    refine ⟨575103810162879909649181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 383402540108586606432787 575103810162879909649181)
                    ·
                      refine ⟨215663928811079966118443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 575103810162879909649181 215663928811079966118443)
                      ·
                        rfl

theorem cell23_420004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_420004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420004 prefixEnd_420004 := by exact prefixLift 420004
  have htrace : WordTrace (prefixWord ++ tailWord_420004) baseStart_420004 baseEnd_420004 := by
    simpa [prefixWord, tailWord_420004, baseEnd_420004] using wordTrace_append hprefix tailTrace_420004
  have hstable : (prefixWord ++ tailWord_420004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420004).length < 2 ^ (prefixWord ++ tailWord_420004).sum := by decide
  have hdescent : baseEnd_420004 < baseStart_420004 := by decide
  rcases family_descends (prefixWord ++ tailWord_420004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420021 : List Nat := [1, 3, 3, 4, 1, 2, 1, 1, 1, 3, 3]
def baseStart_420021 : Nat := 118140960795 + 420021 * 2 ^ 59
def prefixEnd_420021 : Nat := 4983230072969 + 3 ^ 40 * 420021 * 2
def baseEnd_420021 : Nat := 215672657982206399605865

theorem tailTrace_420021 : CollatzResearch.WordTrace tailWord_420021 prefixEnd_420021 215672657982206399605865 := by
  unfold tailWord_420021
  simp only [CollatzResearch.WordTrace]
  refine ⟨15319424411343125720883917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10212949607562083813922611 15319424411343125720883917)
  ·
    refine ⟨5744784154253672145331469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15319424411343125720883917 5744784154253672145331469)
    ·
      refine ⟨2154294057845127054499301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5744784154253672145331469 2154294057845127054499301)
      ·
        refine ⟨403930135845961322718619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2154294057845127054499301 403930135845961322718619)
        ·
          refine ⟨605895203768941984077929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403930135845961322718619 605895203768941984077929)
          ·
            refine ⟨454421402826706488058447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 605895203768941984077929 454421402826706488058447)
            ·
              refine ⟨681632104240059732087671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 454421402826706488058447 681632104240059732087671)
              ·
                refine ⟨1022448156360089598131507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 681632104240059732087671 1022448156360089598131507)
                ·
                  refine ⟨1533672234540134397197261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1022448156360089598131507 1533672234540134397197261)
                  ·
                    refine ⟨575127087952550398948973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1533672234540134397197261 575127087952550398948973)
                    ·
                      refine ⟨215672657982206399605865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 575127087952550398948973 215672657982206399605865)
                      ·
                        rfl

theorem cell23_420021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_420021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420021 prefixEnd_420021 := by exact prefixLift 420021
  have htrace : WordTrace (prefixWord ++ tailWord_420021) baseStart_420021 baseEnd_420021 := by
    simpa [prefixWord, tailWord_420021, baseEnd_420021] using wordTrace_append hprefix tailTrace_420021
  have hstable : (prefixWord ++ tailWord_420021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420021).length < 2 ^ (prefixWord ++ tailWord_420021).sum := by decide
  have hdescent : baseEnd_420021 < baseStart_420021 := by decide
  rcases family_descends (prefixWord ++ tailWord_420021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420034 : List Nat := [3, 5, 1, 1, 1, 1, 1, 1, 2, 2, 5]
def baseStart_420034 : Nat := 118140960795 + 420034 * 2 ^ 59
def prefixEnd_420034 : Nat := 4983230072969 + 3 ^ 40 * 420034 * 2
def baseEnd_420034 : Nat := 215679333230714848743305

theorem tailTrace_420034 : CollatzResearch.WordTrace tailWord_420034 prefixEnd_420034 215679333230714848743305 := by
  unfold tailWord_420034
  simp only [CollatzResearch.WordTrace]
  refine ⟨3829974640074007235276789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10213265706864019294071437 3829974640074007235276789)
  ·
    refine ⟨359060122506938178307199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3829974640074007235276789 359060122506938178307199)
    ·
      refine ⟨538590183760407267460799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359060122506938178307199 538590183760407267460799)
      ·
        refine ⟨807885275640610901191199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538590183760407267460799 807885275640610901191199)
        ·
          refine ⟨1211827913460916351786799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 807885275640610901191199 1211827913460916351786799)
          ·
            refine ⟨1817741870191374527680199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1211827913460916351786799 1817741870191374527680199)
            ·
              refine ⟨2726612805287061791520299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1817741870191374527680199 2726612805287061791520299)
              ·
                refine ⟨4089919207930592687280449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2726612805287061791520299 4089919207930592687280449)
                ·
                  refine ⟨3067439405947944515460337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4089919207930592687280449 3067439405947944515460337)
                  ·
                    refine ⟨2300579554460958386595253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3067439405947944515460337 2300579554460958386595253)
                    ·
                      refine ⟨215679333230714848743305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2300579554460958386595253 215679333230714848743305)
                      ·
                        rfl

theorem cell23_420034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_420034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420034 prefixEnd_420034 := by exact prefixLift 420034
  have htrace : WordTrace (prefixWord ++ tailWord_420034) baseStart_420034 baseEnd_420034 := by
    simpa [prefixWord, tailWord_420034, baseEnd_420034] using wordTrace_append hprefix tailTrace_420034
  have hstable : (prefixWord ++ tailWord_420034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420034).length < 2 ^ (prefixWord ++ tailWord_420034).sum := by decide
  have hdescent : baseEnd_420034 < baseStart_420034 := by decide
  rcases family_descends (prefixWord ++ tailWord_420034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420061 : List Nat := [1, 4, 3, 2, 1, 1, 2, 1, 4, 2, 2]
def baseStart_420061 : Nat := 118140960795 + 420061 * 2 ^ 59
def prefixEnd_420061 : Nat := 4983230072969 + 3 ^ 40 * 420061 * 2
def baseEnd_420061 : Nat := 215693197208386243105681

theorem tailTrace_420061 : CollatzResearch.WordTrace tailWord_420061 prefixEnd_420061 215693197208386243105681 := by
  unfold tailWord_420061
  simp only [CollatzResearch.WordTrace]
  refine ⟨15320883331198212552340037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10213922220798808368226691 15320883331198212552340037)
  ·
    refine ⟨2872665624599664853563757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15320883331198212552340037 2872665624599664853563757)
    ·
      refine ⟨1077249609224874320086409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2872665624599664853563757 1077249609224874320086409)
      ·
        refine ⟨807937206918655740064807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1077249609224874320086409 807937206918655740064807)
        ·
          refine ⟨1211905810377983610097211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 807937206918655740064807 1211905810377983610097211)
          ·
            refine ⟨1817858715566975415145817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1211905810377983610097211 1817858715566975415145817)
            ·
              refine ⟨1363394036675231561359363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1817858715566975415145817 1363394036675231561359363)
              ·
                refine ⟨2045091055012847342039045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1363394036675231561359363 2045091055012847342039045)
                ·
                  refine ⟨383454572814908876632321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2045091055012847342039045 383454572814908876632321)
                  ·
                    refine ⟨287590929611181657474241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 383454572814908876632321 287590929611181657474241)
                    ·
                      refine ⟨215693197208386243105681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 287590929611181657474241 215693197208386243105681)
                      ·
                        rfl

theorem cell23_420061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_420061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420061 prefixEnd_420061 := by exact prefixLift 420061
  have htrace : WordTrace (prefixWord ++ tailWord_420061) baseStart_420061 baseEnd_420061 := by
    simpa [prefixWord, tailWord_420061, baseEnd_420061] using wordTrace_append hprefix tailTrace_420061
  have hstable : (prefixWord ++ tailWord_420061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420061).length < 2 ^ (prefixWord ++ tailWord_420061).sum := by decide
  have hdescent : baseEnd_420061 < baseStart_420061 := by decide
  rcases family_descends (prefixWord ++ tailWord_420061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420097 : List Nat := [1, 2, 4, 1, 1, 2, 4, 1, 2, 5]
def baseStart_420097 : Nat := 118140960795 + 420097 * 2 ^ 59
def prefixEnd_420097 : Nat := 4983230072969 + 3 ^ 40 * 420097 * 2
def baseEnd_420097 : Nat := 71903894170649367418505

theorem tailTrace_420097 : CollatzResearch.WordTrace tailWord_420097 prefixEnd_420097 71903894170649367418505 := by
  unfold tailWord_420097
  simp only [CollatzResearch.WordTrace]
  refine ⟨15322196359067790700650545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10214797572711860467100363 15322196359067790700650545)
  ·
    refine ⟨11491647269300843025487909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15322196359067790700650545 11491647269300843025487909)
    ·
      refine ⟨2154683862993908067278983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11491647269300843025487909 2154683862993908067278983)
      ·
        refine ⟨3232025794490862100918475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2154683862993908067278983 3232025794490862100918475)
        ·
          refine ⟨4848038691736293151377713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3232025794490862100918475 4848038691736293151377713)
          ·
            refine ⟨3636029018802219863533285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4848038691736293151377713 3636029018802219863533285)
            ·
              refine ⟨681755441025416224412491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3636029018802219863533285 681755441025416224412491)
              ·
                refine ⟨1022633161538124336618737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 681755441025416224412491 1022633161538124336618737)
                ·
                  refine ⟨766974871153593252464053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1022633161538124336618737 766974871153593252464053)
                  ·
                    refine ⟨71903894170649367418505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 766974871153593252464053 71903894170649367418505)
                    ·
                      rfl

theorem cell23_420097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_420097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420097 prefixEnd_420097 := by exact prefixLift 420097
  have htrace : WordTrace (prefixWord ++ tailWord_420097) baseStart_420097 baseEnd_420097 := by
    simpa [prefixWord, tailWord_420097, baseEnd_420097] using wordTrace_append hprefix tailTrace_420097
  have hstable : (prefixWord ++ tailWord_420097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420097).length < 2 ^ (prefixWord ++ tailWord_420097).sum := by decide
  have hdescent : baseEnd_420097 < baseStart_420097 := by decide
  rcases family_descends (prefixWord ++ tailWord_420097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420117 : List Nat := [1, 3, 2, 1, 2, 1, 4, 2, 2, 1, 4]
def baseStart_420117 : Nat := 118140960795 + 420117 * 2 ^ 59
def prefixEnd_420117 : Nat := 4983230072969 + 3 ^ 40 * 420117 * 2
def baseEnd_420117 : Nat := 215721952125038024005423

theorem tailTrace_420117 : CollatzResearch.WordTrace tailWord_420117 prefixEnd_420117 215721952125038024005423 := by
  unfold tailWord_420117
  simp only [CollatzResearch.WordTrace]
  refine ⟨15322925818995334116378605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10215283879330222744252403 15322925818995334116378605)
  ·
    refine ⟨5746097182123250293641977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15322925818995334116378605 5746097182123250293641977)
    ·
      refine ⟨4309572886592437720231483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5746097182123250293641977 4309572886592437720231483)
      ·
        refine ⟨6464359329888656580347225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4309572886592437720231483 6464359329888656580347225)
        ·
          refine ⟨4848269497416492435260419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6464359329888656580347225 4848269497416492435260419)
          ·
            refine ⟨7272404246124738652890629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4848269497416492435260419 7272404246124738652890629)
            ·
              refine ⟨1363575796148388497416993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7272404246124738652890629 1363575796148388497416993)
              ·
                refine ⟨1022681847111291373062745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1363575796148388497416993 1022681847111291373062745)
                ·
                  refine ⟨767011385333468529797059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1022681847111291373062745 767011385333468529797059)
                  ·
                    refine ⟨1150517078000202794695589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 767011385333468529797059 1150517078000202794695589)
                    ·
                      refine ⟨215721952125038024005423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1150517078000202794695589 215721952125038024005423)
                      ·
                        rfl

theorem cell23_420117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_420117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420117 prefixEnd_420117 := by exact prefixLift 420117
  have htrace : WordTrace (prefixWord ++ tailWord_420117) baseStart_420117 baseEnd_420117 := by
    simpa [prefixWord, tailWord_420117, baseEnd_420117] using wordTrace_append hprefix tailTrace_420117
  have hstable : (prefixWord ++ tailWord_420117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420117).length < 2 ^ (prefixWord ++ tailWord_420117).sum := by decide
  have hdescent : baseEnd_420117 < baseStart_420117 := by decide
  rcases family_descends (prefixWord ++ tailWord_420117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420120 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 2, 3, 5]
def baseStart_420120 : Nat := 118140960795 + 420120 * 2 ^ 59
def prefixEnd_420120 : Nat := 4983230072969 + 3 ^ 40 * 420120 * 2
def baseEnd_420120 : Nat := 215723492567001512267909

theorem tailTrace_420120 : CollatzResearch.WordTrace tailWord_420120 prefixEnd_420120 215723492567001512267909 := by
  unfold tailWord_420120
  simp only [CollatzResearch.WordTrace]
  refine ⟨7661517618992232814368907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10215356825322977085825209 7661517618992232814368907)
  ·
    refine ⟨11492276428488349221553361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7661517618992232814368907 11492276428488349221553361)
    ·
      refine ⟨8619207321366261916165021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11492276428488349221553361 8619207321366261916165021)
      ·
        refine ⟨3232202745512348218561883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8619207321366261916165021 3232202745512348218561883)
        ·
          refine ⟨4848304118268522327842825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3232202745512348218561883 4848304118268522327842825)
          ·
            refine ⟨3636228088701391745882119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4848304118268522327842825 3636228088701391745882119)
            ·
              refine ⟨5454342133052087618823179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3636228088701391745882119 5454342133052087618823179)
              ·
                refine ⟨8181513199578131428234769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5454342133052087618823179 8181513199578131428234769)
                ·
                  refine ⟨6136134899683598571176077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8181513199578131428234769 6136134899683598571176077)
                  ·
                    refine ⟨2301050587381349464191029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6136134899683598571176077 2301050587381349464191029)
                    ·
                      refine ⟨215723492567001512267909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2301050587381349464191029 215723492567001512267909)
                      ·
                        rfl

theorem cell23_420120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_420120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420120 prefixEnd_420120 := by exact prefixLift 420120
  have htrace : WordTrace (prefixWord ++ tailWord_420120) baseStart_420120 baseEnd_420120 := by
    simpa [prefixWord, tailWord_420120, baseEnd_420120] using wordTrace_append hprefix tailTrace_420120
  have hstable : (prefixWord ++ tailWord_420120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420120).length < 2 ^ (prefixWord ++ tailWord_420120).sum := by decide
  have hdescent : baseEnd_420120 < baseStart_420120 := by decide
  rcases family_descends (prefixWord ++ tailWord_420120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420154 : List Nat := [3, 1, 1, 1, 4, 2, 3, 1, 2, 2, 3]
def baseStart_420154 : Nat := 118140960795 + 420154 * 2 ^ 59
def prefixEnd_420154 : Nat := 4983230072969 + 3 ^ 40 * 420154 * 2
def baseEnd_420154 : Nat := 215740950909254379242753

theorem tailTrace_420154 : CollatzResearch.WordTrace tailWord_420154 prefixEnd_420154 215740950909254379242753 := by
  unfold tailWord_420154
  simp only [CollatzResearch.WordTrace]
  refine ⟨3831068829965322358868879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10216183546574192956983677 3831068829965322358868879)
  ·
    refine ⟨5746603244947983538303319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3831068829965322358868879 5746603244947983538303319)
    ·
      refine ⟨8619904867421975307454979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5746603244947983538303319 8619904867421975307454979)
      ·
        refine ⟨12929857301132962961182469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8619904867421975307454979 12929857301132962961182469)
        ·
          refine ⟨2424348243962430555221713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12929857301132962961182469 2424348243962430555221713)
          ·
            refine ⟨1818261182971822916416285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2424348243962430555221713 1818261182971822916416285)
            ·
              refine ⟨681847943614433593656107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1818261182971822916416285 681847943614433593656107)
              ·
                refine ⟨1022771915421650390484161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 681847943614433593656107 1022771915421650390484161)
                ·
                  refine ⟨767078936566237792863121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1022771915421650390484161 767078936566237792863121)
                  ·
                    refine ⟨575309202424678344647341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 767078936566237792863121 575309202424678344647341)
                    ·
                      refine ⟨215740950909254379242753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 575309202424678344647341 215740950909254379242753)
                      ·
                        rfl

theorem cell23_420154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 1, 2, 2, 3].length) (baseStart_420154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420154 prefixEnd_420154 := by exact prefixLift 420154
  have htrace : WordTrace (prefixWord ++ tailWord_420154) baseStart_420154 baseEnd_420154 := by
    simpa [prefixWord, tailWord_420154, baseEnd_420154] using wordTrace_append hprefix tailTrace_420154
  have hstable : (prefixWord ++ tailWord_420154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420154).length < 2 ^ (prefixWord ++ tailWord_420154).sum := by decide
  have hdescent : baseEnd_420154 < baseStart_420154 := by decide
  rcases family_descends (prefixWord ++ tailWord_420154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420264 : List Nat := [2, 1, 6, 1, 1, 1, 2, 9]
def baseStart_420264 : Nat := 118140960795 + 420264 * 2 ^ 59
def prefixEnd_420264 : Nat := 4983230072969 + 3 ^ 40 * 420264 * 2
def baseEnd_420264 : Nat := 7992497547453664772861

theorem tailTrace_420264 : CollatzResearch.WordTrace tailWord_420264 prefixEnd_420264 7992497547453664772861 := by
  unfold tailWord_420264
  simp only [CollatzResearch.WordTrace]
  refine ⟨7664143674731389110989923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10218858232975185481319897 7664143674731389110989923)
  ·
    refine ⟨11496215512097083666484885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7664143674731389110989923 11496215512097083666484885)
    ·
      refine ⟨538885102129550796866479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11496215512097083666484885 538885102129550796866479)
      ·
        refine ⟨808327653194326195299719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538885102129550796866479 808327653194326195299719)
        ·
          refine ⟨1212491479791489292949579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 808327653194326195299719 1212491479791489292949579)
          ·
            refine ⟨1818737219687233939424369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1212491479791489292949579 1818737219687233939424369)
            ·
              refine ⟨1364052914765425454568277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1818737219687233939424369 1364052914765425454568277)
              ·
                refine ⟨7992497547453664772861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1364052914765425454568277 7992497547453664772861)
                ·
                  rfl

theorem cell23_420264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 9].length) (baseStart_420264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420264 prefixEnd_420264 := by exact prefixLift 420264
  have htrace : WordTrace (prefixWord ++ tailWord_420264) baseStart_420264 baseEnd_420264 := by
    simpa [prefixWord, tailWord_420264, baseEnd_420264] using wordTrace_append hprefix tailTrace_420264
  have hstable : (prefixWord ++ tailWord_420264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420264).length < 2 ^ (prefixWord ++ tailWord_420264).sum := by decide
  have hdescent : baseEnd_420264 < baseStart_420264 := by decide
  rcases family_descends (prefixWord ++ tailWord_420264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420274 : List Nat := [3, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3]
def baseStart_420274 : Nat := 118140960795 + 420274 * 2 ^ 59
def prefixEnd_420274 : Nat := 4983230072969 + 3 ^ 40 * 420274 * 2
def baseEnd_420274 : Nat := 215802568587793909742201

theorem tailTrace_420274 : CollatzResearch.WordTrace tailWord_420274 prefixEnd_420274 215802568587793909742201 := by
  unfold tailWord_420274
  simp only [CollatzResearch.WordTrace]
  refine ⟨3832163019856637482460969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10219101386284366619895917 3832163019856637482460969)
  ·
    refine ⟨2874122264892478111845727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3832163019856637482460969 2874122264892478111845727)
    ·
      refine ⟨4311183397338717167768591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2874122264892478111845727 4311183397338717167768591)
      ·
        refine ⟨6466775096008075751652887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4311183397338717167768591 6466775096008075751652887)
        ·
          refine ⟨9700162644012113627479331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6466775096008075751652887 9700162644012113627479331)
          ·
            refine ⟨14550243966018170441218997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9700162644012113627479331 14550243966018170441218997)
            ·
              refine ⟨1364085371814203478864281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14550243966018170441218997 1364085371814203478864281)
              ·
                refine ⟨1023064028860652609148211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1364085371814203478864281 1023064028860652609148211)
                ·
                  refine ⟨1534596043290978913722317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1023064028860652609148211 1534596043290978913722317)
                  ·
                    refine ⟨575473516234117092645869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1534596043290978913722317 575473516234117092645869)
                    ·
                      refine ⟨215802568587793909742201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 575473516234117092645869 215802568587793909742201)
                      ·
                        rfl

theorem cell23_420274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3].length) (baseStart_420274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420274 prefixEnd_420274 := by exact prefixLift 420274
  have htrace : WordTrace (prefixWord ++ tailWord_420274) baseStart_420274 baseEnd_420274 := by
    simpa [prefixWord, tailWord_420274, baseEnd_420274] using wordTrace_append hprefix tailTrace_420274
  have hstable : (prefixWord ++ tailWord_420274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420274).length < 2 ^ (prefixWord ++ tailWord_420274).sum := by decide
  have hdescent : baseEnd_420274 < baseStart_420274 := by decide
  rcases family_descends (prefixWord ++ tailWord_420274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420292 : List Nat := [2, 3, 3, 2, 2, 1, 1, 4, 1, 2, 2]
def baseStart_420292 : Nat := 118140960795 + 420292 * 2 ^ 59
def prefixEnd_420292 : Nat := 4983230072969 + 3 ^ 40 * 420292 * 2
def baseEnd_420292 : Nat := 215811811239574839317119

theorem tailTrace_420292 : CollatzResearch.WordTrace tailWord_420292 prefixEnd_420292 215811811239574839317119 := by
  unfold tailWord_420292
  simp only [CollatzResearch.WordTrace]
  refine ⟨7664654296680669501999565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10219539062240892669332753 7664654296680669501999565)
  ·
    refine ⟨2874245361255251063249837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7664654296680669501999565 2874245361255251063249837)
    ·
      refine ⟨1077842010470719148718689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2874245361255251063249837 1077842010470719148718689)
      ·
        refine ⟨808381507853039361539017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1077842010470719148718689 808381507853039361539017)
        ·
          refine ⟨606286130889779521154263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 808381507853039361539017 606286130889779521154263)
          ·
            refine ⟨909429196334669281731395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606286130889779521154263 909429196334669281731395)
            ·
              refine ⟨1364143794502003922597093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 909429196334669281731395 1364143794502003922597093)
              ·
                refine ⟨255776961469125735486955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1364143794502003922597093 255776961469125735486955)
                ·
                  refine ⟨383665442203688603230433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 255776961469125735486955 383665442203688603230433)
                  ·
                    refine ⟨287749081652766452422825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 383665442203688603230433 287749081652766452422825)
                    ·
                      refine ⟨215811811239574839317119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 287749081652766452422825 215811811239574839317119)
                      ·
                        rfl

theorem cell23_420292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_420292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420292 prefixEnd_420292 := by exact prefixLift 420292
  have htrace : WordTrace (prefixWord ++ tailWord_420292) baseStart_420292 baseEnd_420292 := by
    simpa [prefixWord, tailWord_420292, baseEnd_420292] using wordTrace_append hprefix tailTrace_420292
  have hstable : (prefixWord ++ tailWord_420292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420292).length < 2 ^ (prefixWord ++ tailWord_420292).sum := by decide
  have hdescent : baseEnd_420292 < baseStart_420292 := by decide
  rcases family_descends (prefixWord ++ tailWord_420292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420297 : List Nat := [1, 2, 1, 1, 2, 1, 5, 1, 2, 3, 4]
def baseStart_420297 : Nat := 118140960795 + 420297 * 2 ^ 59
def prefixEnd_420297 : Nat := 4983230072969 + 3 ^ 40 * 420297 * 2
def baseEnd_420297 : Nat := 215814378642847319754595

theorem tailTrace_420297 : CollatzResearch.WordTrace tailWord_420297 prefixEnd_420297 215814378642847319754595 := by
  unfold tailWord_420297
  simp only [CollatzResearch.WordTrace]
  refine ⟨15329490958343224857931145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10219660638895483238620763 15329490958343224857931145)
  ·
    refine ⟨11497118218757418643448359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15329490958343224857931145 11497118218757418643448359)
    ·
      refine ⟨17245677328136127965172539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11497118218757418643448359 17245677328136127965172539)
      ·
        refine ⟨25868515992204191947758809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17245677328136127965172539 25868515992204191947758809)
        ·
          refine ⟨19401386994153143960819107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25868515992204191947758809 19401386994153143960819107)
          ·
            refine ⟨29102080491229715941228661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19401386994153143960819107 29102080491229715941228661)
            ·
              refine ⟨2728320046052785869490187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29102080491229715941228661 2728320046052785869490187)
              ·
                refine ⟨4092480069079178804235281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2728320046052785869490187 4092480069079178804235281)
                ·
                  refine ⟨3069360051809384103176461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4092480069079178804235281 3069360051809384103176461)
                  ·
                    refine ⟨1151010019428519038691173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3069360051809384103176461 1151010019428519038691173)
                    ·
                      refine ⟨215814378642847319754595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1151010019428519038691173 215814378642847319754595)
                      ·
                        rfl

theorem cell23_420297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 3, 4].length) (baseStart_420297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420297 prefixEnd_420297 := by exact prefixLift 420297
  have htrace : WordTrace (prefixWord ++ tailWord_420297) baseStart_420297 baseEnd_420297 := by
    simpa [prefixWord, tailWord_420297, baseEnd_420297] using wordTrace_append hprefix tailTrace_420297
  have hstable : (prefixWord ++ tailWord_420297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420297).length < 2 ^ (prefixWord ++ tailWord_420297).sum := by decide
  have hdescent : baseEnd_420297 < baseStart_420297 := by decide
  rcases family_descends (prefixWord ++ tailWord_420297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420308 : List Nat := [2, 4, 1, 2, 2, 1, 2, 3, 2, 1, 3]
def baseStart_420308 : Nat := 118140960795 + 420308 * 2 ^ 59
def prefixEnd_420308 : Nat := 4983230072969 + 3 ^ 40 * 420308 * 2
def baseEnd_420308 : Nat := 215820026930046776717045

theorem tailTrace_420308 : CollatzResearch.WordTrace tailWord_420308 prefixEnd_420308 215820026930046776717045 := by
  unfold tailWord_420308
  simp only [CollatzResearch.WordTrace]
  refine ⟨7664946080651686868290789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10219928107535582491054385 7664946080651686868290789)
  ·
    refine ⟨1437177390122191287804523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7664946080651686868290789 1437177390122191287804523)
    ·
      refine ⟨2155766085183286931706785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1437177390122191287804523 2155766085183286931706785)
      ·
        refine ⟨1616824563887465198780089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2155766085183286931706785 1616824563887465198780089)
        ·
          refine ⟨1212618422915598899085067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1616824563887465198780089 1212618422915598899085067)
          ·
            refine ⟨1818927634373398348627601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1212618422915598899085067 1818927634373398348627601)
            ·
              refine ⟨1364195725780048761470701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1818927634373398348627601 1364195725780048761470701)
              ·
                refine ⟨511573397167518285551513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1364195725780048761470701 511573397167518285551513)
                ·
                  refine ⟨383680047875638714163635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 511573397167518285551513 383680047875638714163635)
                  ·
                    refine ⟨575520071813458071245453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 383680047875638714163635 575520071813458071245453)
                    ·
                      refine ⟨215820026930046776717045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 575520071813458071245453 215820026930046776717045)
                      ·
                        rfl

theorem cell23_420308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_420308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420308 prefixEnd_420308 := by exact prefixLift 420308
  have htrace : WordTrace (prefixWord ++ tailWord_420308) baseStart_420308 baseEnd_420308 := by
    simpa [prefixWord, tailWord_420308, baseEnd_420308] using wordTrace_append hprefix tailTrace_420308
  have hstable : (prefixWord ++ tailWord_420308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420308).length < 2 ^ (prefixWord ++ tailWord_420308).sum := by decide
  have hdescent : baseEnd_420308 < baseStart_420308 := by decide
  rcases family_descends (prefixWord ++ tailWord_420308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420331 : List Nat := [1, 1, 1, 1, 2, 3, 4, 2, 4, 2, 2]
def baseStart_420331 : Nat := 118140960795 + 420331 * 2 ^ 59
def prefixEnd_420331 : Nat := 4983230072969 + 3 ^ 40 * 420331 * 2
def baseEnd_420331 : Nat := 215831836985100186729439

theorem tailTrace_420331 : CollatzResearch.WordTrace tailWord_420331 prefixEnd_420331 215831836985100186729439 := by
  unfold tailWord_420331
  simp only [CollatzResearch.WordTrace]
  refine ⟨15330731040220048664668847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10220487360146699109779231 15330731040220048664668847)
  ·
    refine ⟨22996096560330072997003271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15330731040220048664668847 22996096560330072997003271)
    ·
      refine ⟨34494144840495109495504907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22996096560330072997003271 34494144840495109495504907)
      ·
        refine ⟨51741217260742664243257361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34494144840495109495504907 51741217260742664243257361)
        ·
          refine ⟨38805912945556998182443021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51741217260742664243257361 38805912945556998182443021)
          ·
            refine ⟨14552217354583874318416133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38805912945556998182443021 14552217354583874318416133)
            ·
              refine ⟨2728540753984476434703025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14552217354583874318416133 2728540753984476434703025)
              ·
                refine ⟨2046405565488357326027269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2728540753984476434703025 2046405565488357326027269)
                ·
                  refine ⟨383701043529066998630113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2046405565488357326027269 383701043529066998630113)
                  ·
                    refine ⟨287775782646800248972585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 383701043529066998630113 287775782646800248972585)
                    ·
                      refine ⟨215831836985100186729439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 287775782646800248972585 215831836985100186729439)
                      ·
                        rfl

theorem cell23_420331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 4, 2, 2].length) (baseStart_420331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420331 prefixEnd_420331 := by exact prefixLift 420331
  have htrace : WordTrace (prefixWord ++ tailWord_420331) baseStart_420331 baseEnd_420331 := by
    simpa [prefixWord, tailWord_420331, baseEnd_420331] using wordTrace_append hprefix tailTrace_420331
  have hstable : (prefixWord ++ tailWord_420331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420331).length < 2 ^ (prefixWord ++ tailWord_420331).sum := by decide
  have hdescent : baseEnd_420331 < baseStart_420331 := by decide
  rcases family_descends (prefixWord ++ tailWord_420331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420337 : List Nat := [1, 2, 2, 2, 3, 1, 1, 2, 9]
def baseStart_420337 : Nat := 118140960795 + 420337 * 2 ^ 59
def prefixEnd_420337 : Nat := 4983230072969 + 3 ^ 40 * 420337 * 2
def baseEnd_420337 : Nat := 23981657541003018139379

theorem tailTrace_420337 : CollatzResearch.WordTrace tailWord_420337 prefixEnd_420337 23981657541003018139379 := by
  unfold tailWord_420337
  simp only [CollatzResearch.WordTrace]
  refine ⟨15330949878198311689387265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10220633252132207792924843 15330949878198311689387265)
  ·
    refine ⟨11498212408648733767040449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15330949878198311689387265 11498212408648733767040449)
    ·
      refine ⟨8623659306486550325280337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11498212408648733767040449 8623659306486550325280337)
      ·
        refine ⟨6467744479864912743960253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8623659306486550325280337 6467744479864912743960253)
        ·
          refine ⟨2425404179949342278985095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6467744479864912743960253 2425404179949342278985095)
          ·
            refine ⟨3638106269924013418477643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2425404179949342278985095 3638106269924013418477643)
            ·
              refine ⟨5457159404886020127716465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3638106269924013418477643 5457159404886020127716465)
              ·
                refine ⟨4092869553664515095787349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5457159404886020127716465 4092869553664515095787349)
                ·
                  refine ⟨23981657541003018139379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4092869553664515095787349 23981657541003018139379)
                  ·
                    rfl

theorem cell23_420337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 9].length) (baseStart_420337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420337 prefixEnd_420337 := by exact prefixLift 420337
  have htrace : WordTrace (prefixWord ++ tailWord_420337) baseStart_420337 baseEnd_420337 := by
    simpa [prefixWord, tailWord_420337, baseEnd_420337] using wordTrace_append hprefix tailTrace_420337
  have hstable : (prefixWord ++ tailWord_420337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420337).length < 2 ^ (prefixWord ++ tailWord_420337).sum := by decide
  have hdescent : baseEnd_420337 < baseStart_420337 := by decide
  rcases family_descends (prefixWord ++ tailWord_420337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420367 : List Nat := [1, 1, 2, 1, 1, 1, 2, 6, 1, 7]
def baseStart_420367 : Nat := 118140960795 + 420367 * 2 ^ 59
def prefixEnd_420367 : Nat := 4983230072969 + 3 ^ 40 * 420367 * 2
def baseEnd_420367 : Nat := 71950107429554015293091

theorem tailTrace_420367 : CollatzResearch.WordTrace tailWord_420367 prefixEnd_420367 71950107429554015293091 := by
  unfold tailWord_420367
  simp only [CollatzResearch.WordTrace]
  refine ⟨15332044068089626812979355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10221362712059751208652903 15332044068089626812979355)
  ·
    refine ⟨22998066102134440219469033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15332044068089626812979355 22998066102134440219469033)
    ·
      refine ⟨17248549576600830164601775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22998066102134440219469033 17248549576600830164601775)
      ·
        refine ⟨25872824364901245246902663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17248549576600830164601775 25872824364901245246902663)
        ·
          refine ⟨38809236547351867870353995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25872824364901245246902663 38809236547351867870353995)
          ·
            refine ⟨58213854821027801805530993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38809236547351867870353995 58213854821027801805530993)
            ·
              refine ⟨43660391115770851354148245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58213854821027801805530993 43660391115770851354148245)
              ·
                refine ⟨2046580833551758657225699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43660391115770851354148245 2046580833551758657225699)
                ·
                  refine ⟨3069871250327637985838549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2046580833551758657225699 3069871250327637985838549)
                  ·
                    refine ⟨71950107429554015293091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3069871250327637985838549 71950107429554015293091)
                    ·
                      rfl

theorem cell23_420367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 7].length) (baseStart_420367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420367 prefixEnd_420367 := by exact prefixLift 420367
  have htrace : WordTrace (prefixWord ++ tailWord_420367) baseStart_420367 baseEnd_420367 := by
    simpa [prefixWord, tailWord_420367, baseEnd_420367] using wordTrace_append hprefix tailTrace_420367
  have hstable : (prefixWord ++ tailWord_420367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420367).length < 2 ^ (prefixWord ++ tailWord_420367).sum := by decide
  have hdescent : baseEnd_420367 < baseStart_420367 := by decide
  rcases family_descends (prefixWord ++ tailWord_420367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420377 : List Nat := [1, 2, 1, 2, 1, 1, 2, 4, 1, 1, 7]
def baseStart_420377 : Nat := 118140960795 + 420377 * 2 ^ 59
def prefixEnd_420377 : Nat := 4983230072969 + 3 ^ 40 * 420377 * 2
def baseEnd_420377 : Nat := 215855457095207006754227

theorem tailTrace_420377 : CollatzResearch.WordTrace tailWord_420377 prefixEnd_420377 215855457095207006754227 := by
  unfold tailWord_420377
  simp only [CollatzResearch.WordTrace]
  refine ⟨15332408798053398520843385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10221605865368932347228923 15332408798053398520843385)
  ·
    refine ⟨11499306598540048890632539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15332408798053398520843385 11499306598540048890632539)
    ·
      refine ⟨17248959897810073335948809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11499306598540048890632539 17248959897810073335948809)
      ·
        refine ⟨12936719923357555001961607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17248959897810073335948809 12936719923357555001961607)
        ·
          refine ⟨19405079885036332502942411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12936719923357555001961607 19405079885036332502942411)
          ·
            refine ⟨29107619827554498754413617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19405079885036332502942411 29107619827554498754413617)
            ·
              refine ⟨21830714870665874065810213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29107619827554498754413617 21830714870665874065810213)
              ·
                refine ⟨4093259038249851387339415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21830714870665874065810213 4093259038249851387339415)
                ·
                  refine ⟨6139888557374777081009123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4093259038249851387339415 6139888557374777081009123)
                  ·
                    refine ⟨9209832836062165621513685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6139888557374777081009123 9209832836062165621513685)
                    ·
                      refine ⟨215855457095207006754227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 9209832836062165621513685 215855457095207006754227)
                      ·
                        rfl

theorem cell23_420377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_420377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420377 prefixEnd_420377 := by exact prefixLift 420377
  have htrace : WordTrace (prefixWord ++ tailWord_420377) baseStart_420377 baseEnd_420377 := by
    simpa [prefixWord, tailWord_420377, baseEnd_420377] using wordTrace_append hprefix tailTrace_420377
  have hstable : (prefixWord ++ tailWord_420377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420377).length < 2 ^ (prefixWord ++ tailWord_420377).sum := by decide
  have hdescent : baseEnd_420377 < baseStart_420377 := by decide
  rcases family_descends (prefixWord ++ tailWord_420377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420424 : List Nat := [2, 1, 3, 1, 1, 1, 1, 3, 3, 4, 3]
def baseStart_420424 : Nat := 118140960795 + 420424 * 2 ^ 59
def prefixEnd_420424 : Nat := 4983230072969 + 3 ^ 40 * 420424 * 2
def baseEnd_420424 : Nat := 215879590685968322866511

theorem tailTrace_420424 : CollatzResearch.WordTrace tailWord_420424 prefixEnd_420424 215879590685968322866511 := by
  unfold tailWord_420424
  simp only [CollatzResearch.WordTrace]
  refine ⟨7667061514441562773902163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10222748685922083698536217 7667061514441562773902163)
  ·
    refine ⟨11500592271662344160853245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7667061514441562773902163 11500592271662344160853245)
    ·
      refine ⟨4312722101873379060319967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11500592271662344160853245 4312722101873379060319967)
      ·
        refine ⟨6469083152810068590479951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4312722101873379060319967 6469083152810068590479951)
        ·
          refine ⟨9703624729215102885719927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6469083152810068590479951 9703624729215102885719927)
          ·
            refine ⟨14555437093822654328579891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9703624729215102885719927 14555437093822654328579891)
            ·
              refine ⟨21833155640733981492869837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14555437093822654328579891 21833155640733981492869837)
              ·
                refine ⟨8187433365275243059826189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21833155640733981492869837 8187433365275243059826189)
                ·
                  refine ⟨3070287511978216147434821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8187433365275243059826189 3070287511978216147434821)
                  ·
                    refine ⟨575678908495915527644029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3070287511978216147434821 575678908495915527644029)
                    ·
                      refine ⟨215879590685968322866511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 575678908495915527644029 215879590685968322866511)
                      ·
                        rfl

theorem cell23_420424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 3, 3, 4, 3].length) (baseStart_420424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420424 prefixEnd_420424 := by exact prefixLift 420424
  have htrace : WordTrace (prefixWord ++ tailWord_420424) baseStart_420424 baseEnd_420424 := by
    simpa [prefixWord, tailWord_420424, baseEnd_420424] using wordTrace_append hprefix tailTrace_420424
  have hstable : (prefixWord ++ tailWord_420424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420424).length < 2 ^ (prefixWord ++ tailWord_420424).sum := by decide
  have hdescent : baseEnd_420424 < baseStart_420424 := by decide
  rcases family_descends (prefixWord ++ tailWord_420424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420461 : List Nat := [1, 5, 1, 1, 3, 1, 1, 4, 6]
def baseStart_420461 : Nat := 118140960795 + 420461 * 2 ^ 59
def prefixEnd_420461 : Nat := 4983230072969 + 3 ^ 40 * 420461 * 2
def baseEnd_420461 : Nat := 23988732163353853122649

theorem tailTrace_420461 : CollatzResearch.WordTrace tailWord_420461 prefixEnd_420461 23988732163353853122649 := by
  unfold tailWord_420461
  simp only [CollatzResearch.WordTrace]
  refine ⟨15335472529749080866901237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10223648353166053911267491 15335472529749080866901237)
  ·
    refine ⟨1437700549663976331271991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15335472529749080866901237 1437700549663976331271991)
    ·
      refine ⟨2156550824495964496907987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1437700549663976331271991 2156550824495964496907987)
      ·
        refine ⟨3234826236743946745361981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2156550824495964496907987 3234826236743946745361981)
        ·
          refine ⟨1213059838778980029510743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3234826236743946745361981 1213059838778980029510743)
          ·
            refine ⟨1819589758168470044266115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1213059838778980029510743 1819589758168470044266115)
            ·
              refine ⟨2729384637252705066399173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1819589758168470044266115 2729384637252705066399173)
              ·
                refine ⟨511759619484882199949845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2729384637252705066399173 511759619484882199949845)
                ·
                  refine ⟨23988732163353853122649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 511759619484882199949845 23988732163353853122649)
                  ·
                    rfl

theorem cell23_420461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_420461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420461 prefixEnd_420461 := by exact prefixLift 420461
  have htrace : WordTrace (prefixWord ++ tailWord_420461) baseStart_420461 baseEnd_420461 := by
    simpa [prefixWord, tailWord_420461, baseEnd_420461] using wordTrace_append hprefix tailTrace_420461
  have hstable : (prefixWord ++ tailWord_420461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420461).length < 2 ^ (prefixWord ++ tailWord_420461).sum := by decide
  have hdescent : baseEnd_420461 < baseStart_420461 := by decide
  rcases family_descends (prefixWord ++ tailWord_420461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420505 : List Nat := [1, 2, 1, 2, 1, 2, 6, 3, 1, 1, 3]
def baseStart_420505 : Nat := 118140960795 + 420505 * 2 ^ 59
def prefixEnd_420505 : Nat := 4983230072969 + 3 ^ 40 * 420505 * 2
def baseEnd_420505 : Nat := 215921182618982505953639

theorem tailTrace_420505 : CollatzResearch.WordTrace tailWord_420505 prefixEnd_420505 215921182618982505953639 := by
  unfold tailWord_420505
  simp only [CollatzResearch.WordTrace]
  refine ⟨15337077341589676381502969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10224718227726450921001979 15337077341589676381502969)
  ·
    refine ⟨11502808006192257286127227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15337077341589676381502969 11502808006192257286127227)
    ·
      refine ⟨17254212009288385929190841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11502808006192257286127227 17254212009288385929190841)
      ·
        refine ⟨12940659006966289446893131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17254212009288385929190841 12940659006966289446893131)
        ·
          refine ⟨19410988510449434170339697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12940659006966289446893131 19410988510449434170339697)
          ·
            refine ⟨14558241382837075627754773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19410988510449434170339697 14558241382837075627754773)
            ·
              refine ⟨682417564820487920051005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14558241382837075627754773 682417564820487920051005)
              ·
                refine ⟨255906586807682970019127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 682417564820487920051005 255906586807682970019127)
                ·
                  refine ⟨383859880211524455028691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 255906586807682970019127 383859880211524455028691)
                  ·
                    refine ⟨575789820317286682543037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 383859880211524455028691 575789820317286682543037)
                    ·
                      refine ⟨215921182618982505953639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 575789820317286682543037 215921182618982505953639)
                      ·
                        rfl

theorem cell23_420505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 3, 1, 1, 3].length) (baseStart_420505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420505 prefixEnd_420505 := by exact prefixLift 420505
  have htrace : WordTrace (prefixWord ++ tailWord_420505) baseStart_420505 baseEnd_420505 := by
    simpa [prefixWord, tailWord_420505, baseEnd_420505] using wordTrace_append hprefix tailTrace_420505
  have hstable : (prefixWord ++ tailWord_420505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420505).length < 2 ^ (prefixWord ++ tailWord_420505).sum := by decide
  have hdescent : baseEnd_420505 < baseStart_420505 := by decide
  rcases family_descends (prefixWord ++ tailWord_420505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420508 : List Nat := [2, 2, 3, 2, 2, 2, 1, 3, 1, 5]
def baseStart_420508 : Nat := 118140960795 + 420508 * 2 ^ 59
def prefixEnd_420508 : Nat := 4983230072969 + 3 ^ 40 * 420508 * 2
def baseEnd_420508 : Nat := 71974241020315331405375

theorem tailTrace_420508 : CollatzResearch.WordTrace tailWord_420508 prefixEnd_420508 71974241020315331405375 := by
  unfold tailWord_420508
  simp only [CollatzResearch.WordTrace]
  refine ⟨7668593380289403946931089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10224791173719205262574785 7668593380289403946931089)
  ·
    refine ⟨5751445035217052960198317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7668593380289403946931089 5751445035217052960198317)
    ·
      refine ⟨2156791888206394860074369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5751445035217052960198317 2156791888206394860074369)
      ·
        refine ⟨1617593916154796145055777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2156791888206394860074369 1617593916154796145055777)
        ·
          refine ⟨1213195437116097108791833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1617593916154796145055777 1213195437116097108791833)
          ·
            refine ⟨909896577837072831593875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1213195437116097108791833 909896577837072831593875)
            ·
              refine ⟨1364844866755609247390813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 909896577837072831593875 1364844866755609247390813)
              ·
                refine ⟨511816825033353467771555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1364844866755609247390813 511816825033353467771555)
                ·
                  refine ⟨767725237550030201657333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 511816825033353467771555 767725237550030201657333)
                  ·
                    refine ⟨71974241020315331405375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 767725237550030201657333 71974241020315331405375)
                    ·
                      rfl

theorem cell23_420508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_420508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420508 prefixEnd_420508 := by exact prefixLift 420508
  have htrace : WordTrace (prefixWord ++ tailWord_420508) baseStart_420508 baseEnd_420508 := by
    simpa [prefixWord, tailWord_420508, baseEnd_420508] using wordTrace_append hprefix tailTrace_420508
  have hstable : (prefixWord ++ tailWord_420508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420508).length < 2 ^ (prefixWord ++ tailWord_420508).sum := by decide
  have hdescent : baseEnd_420508 < baseStart_420508 := by decide
  rcases family_descends (prefixWord ++ tailWord_420508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420524 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 4]
def baseStart_420524 : Nat := 118140960795 + 420524 * 2 ^ 59
def prefixEnd_420524 : Nat := 4983230072969 + 3 ^ 40 * 420524 * 2
def baseEnd_420524 : Nat := 215930938751417931616051

theorem tailTrace_420524 : CollatzResearch.WordTrace tailWord_420524 prefixEnd_420524 215930938751417931616051 := by
  unfold tailWord_420524
  simp only [CollatzResearch.WordTrace]
  refine ⟨7668885164260421313222313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10225180219013895084296417 7668885164260421313222313)
  ·
    refine ⟨5751663873195315984916735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7668885164260421313222313 5751663873195315984916735)
    ·
      refine ⟨8627495809792973977375103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5751663873195315984916735 8627495809792973977375103)
      ·
        refine ⟨12941243714689460966062655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8627495809792973977375103 12941243714689460966062655)
        ·
          refine ⟨19411865572034191449093983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12941243714689460966062655 19411865572034191449093983)
          ·
            refine ⟨29117798358051287173640975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19411865572034191449093983 29117798358051287173640975)
            ·
              refine ⟨43676697537076930760461463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29117798358051287173640975 43676697537076930760461463)
              ·
                refine ⟨65515046305615396140692195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43676697537076930760461463 65515046305615396140692195)
                ·
                  refine ⟨98272569458423094211038293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65515046305615396140692195 98272569458423094211038293)
                  ·
                    refine ⟨1151631673340895635285605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98272569458423094211038293 1151631673340895635285605)
                    ·
                      refine ⟨215930938751417931616051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1151631673340895635285605 215930938751417931616051)
                      ·
                        rfl

theorem cell23_420524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 4].length) (baseStart_420524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420524 prefixEnd_420524 := by exact prefixLift 420524
  have htrace : WordTrace (prefixWord ++ tailWord_420524) baseStart_420524 baseEnd_420524 := by
    simpa [prefixWord, tailWord_420524, baseEnd_420524] using wordTrace_append hprefix tailTrace_420524
  have hstable : (prefixWord ++ tailWord_420524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420524).length < 2 ^ (prefixWord ++ tailWord_420524).sum := by decide
  have hdescent : baseEnd_420524 < baseStart_420524 := by decide
  rcases family_descends (prefixWord ++ tailWord_420524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420531 : List Nat := [1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 5]
def baseStart_420531 : Nat := 118140960795 + 420531 * 2 ^ 59
def prefixEnd_420531 : Nat := 4983230072969 + 3 ^ 40 * 420531 * 2
def baseEnd_420531 : Nat := 215934533115999404228519

theorem tailTrace_420531 : CollatzResearch.WordTrace tailWord_420531 prefixEnd_420531 215934533115999404228519 := by
  unfold tailWord_420531
  simp only [CollatzResearch.WordTrace]
  refine ⟨15338025639495482821949447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10225350426330321881299631 15338025639495482821949447)
  ·
    refine ⟨23007038459243224232924171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15338025639495482821949447 23007038459243224232924171)
    ·
      refine ⟨34510557688864836349386257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23007038459243224232924171 34510557688864836349386257)
      ·
        refine ⟨25882918266648627262039693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34510557688864836349386257 25882918266648627262039693)
        ·
          refine ⟨9706094349993235223264885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25882918266648627262039693 9706094349993235223264885)
          ·
            refine ⟨909946345311865802181083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9706094349993235223264885 909946345311865802181083)
            ·
              refine ⟨1364919517967798703271625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 909946345311865802181083 1364919517967798703271625)
              ·
                refine ⟨1023689638475849027453719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1364919517967798703271625 1023689638475849027453719)
                ·
                  refine ⟨1535534457713773541180579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1023689638475849027453719 1535534457713773541180579)
                  ·
                    refine ⟨2303301686570660311770869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1535534457713773541180579 2303301686570660311770869)
                    ·
                      refine ⟨215934533115999404228519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2303301686570660311770869 215934533115999404228519)
                      ·
                        rfl

theorem cell23_420531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 5].length) (baseStart_420531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420531 prefixEnd_420531 := by exact prefixLift 420531
  have htrace : WordTrace (prefixWord ++ tailWord_420531) baseStart_420531 baseEnd_420531 := by
    simpa [prefixWord, tailWord_420531, baseEnd_420531] using wordTrace_append hprefix tailTrace_420531
  have hstable : (prefixWord ++ tailWord_420531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420531).length < 2 ^ (prefixWord ++ tailWord_420531).sum := by decide
  have hdescent : baseEnd_420531 < baseStart_420531 := by decide
  rcases family_descends (prefixWord ++ tailWord_420531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420541 : List Nat := [1, 4, 1, 2, 1, 4, 1, 1, 1, 1, 6]
def baseStart_420541 : Nat := 118140960795 + 420541 * 2 ^ 59
def prefixEnd_420541 : Nat := 4983230072969 + 3 ^ 40 * 420541 * 2
def baseEnd_420541 : Nat := 215939667922544365103473

theorem tailTrace_420541 : CollatzResearch.WordTrace tailWord_420541 prefixEnd_420541 215939667922544365103473 := by
  unfold tailWord_420541
  simp only [CollatzResearch.WordTrace]
  refine ⟨15338390369459254529813477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10225593579639503019875651 15338390369459254529813477)
  ·
    refine ⟨2875948194273610224340027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15338390369459254529813477 2875948194273610224340027)
    ·
      refine ⟨4313922291410415336510041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2875948194273610224340027 4313922291410415336510041)
      ·
        refine ⟨3235441718557811502382531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4313922291410415336510041 3235441718557811502382531)
        ·
          refine ⟨4853162577836717253573797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3235441718557811502382531 4853162577836717253573797)
          ·
            refine ⟨909967983344384485045087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4853162577836717253573797 909967983344384485045087)
            ·
              refine ⟨1364951975016576727567631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 909967983344384485045087 1364951975016576727567631)
              ·
                refine ⟨2047427962524865091351447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1364951975016576727567631 2047427962524865091351447)
                ·
                  refine ⟨3071141943787297637027171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2047427962524865091351447 3071141943787297637027171)
                  ·
                    refine ⟨4606712915680946455540757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3071141943787297637027171 4606712915680946455540757)
                    ·
                      refine ⟨215939667922544365103473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4606712915680946455540757 215939667922544365103473)
                      ·
                        rfl

theorem cell23_420541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_420541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420541 prefixEnd_420541 := by exact prefixLift 420541
  have htrace : WordTrace (prefixWord ++ tailWord_420541) baseStart_420541 baseEnd_420541 := by
    simpa [prefixWord, tailWord_420541, baseEnd_420541] using wordTrace_append hprefix tailTrace_420541
  have hstable : (prefixWord ++ tailWord_420541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420541).length < 2 ^ (prefixWord ++ tailWord_420541).sum := by decide
  have hdescent : baseEnd_420541 < baseStart_420541 := by decide
  rcases family_descends (prefixWord ++ tailWord_420541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420561 : List Nat := [1, 2, 2, 1, 2, 3, 2, 1, 3, 3, 3]
def baseStart_420561 : Nat := 118140960795 + 420561 * 2 ^ 59
def prefixEnd_420561 : Nat := 4983230072969 + 3 ^ 40 * 420561 * 2
def baseEnd_420561 : Nat := 215949937535634286853381

theorem tailTrace_420561 : CollatzResearch.WordTrace tailWord_420561 prefixEnd_420561 215949937535634286853381 := by
  unfold tailWord_420561
  simp only [CollatzResearch.WordTrace]
  refine ⟨15339119829386797945541537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10226079886257865297027691 15339119829386797945541537)
  ·
    refine ⟨11504339872040098459156153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15339119829386797945541537 11504339872040098459156153)
    ·
      refine ⟨8628254904030073844367115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11504339872040098459156153 8628254904030073844367115)
      ·
        refine ⟨12942382356045110766550673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8628254904030073844367115 12942382356045110766550673)
        ·
          refine ⟨9706786767033833074913005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12942382356045110766550673 9706786767033833074913005)
          ·
            refine ⟨3640045037637687403092377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9706786767033833074913005 3640045037637687403092377)
            ·
              refine ⟨2730033778228265552319283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3640045037637687403092377 2730033778228265552319283)
              ·
                refine ⟨4095050667342398328478925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2730033778228265552319283 4095050667342398328478925)
                ·
                  refine ⟨1535644000253399373179597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4095050667342398328478925 1535644000253399373179597)
                  ·
                    refine ⟨575866500095024764942349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1535644000253399373179597 575866500095024764942349)
                    ·
                      refine ⟨215949937535634286853381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 575866500095024764942349 215949937535634286853381)
                      ·
                        rfl

theorem cell23_420561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 3, 3].length) (baseStart_420561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420561 prefixEnd_420561 := by exact prefixLift 420561
  have htrace : WordTrace (prefixWord ++ tailWord_420561) baseStart_420561 baseEnd_420561 := by
    simpa [prefixWord, tailWord_420561, baseEnd_420561] using wordTrace_append hprefix tailTrace_420561
  have hstable : (prefixWord ++ tailWord_420561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420561).length < 2 ^ (prefixWord ++ tailWord_420561).sum := by decide
  have hdescent : baseEnd_420561 < baseStart_420561 := by decide
  rcases family_descends (prefixWord ++ tailWord_420561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420565 : List Nat := [1, 3, 2, 5, 1, 1, 2, 1, 1, 1, 5]
def baseStart_420565 : Nat := 118140960795 + 420565 * 2 ^ 59
def prefixEnd_420565 : Nat := 4983230072969 + 3 ^ 40 * 420565 * 2
def baseEnd_420565 : Nat := 215951991458252271203363

theorem tailTrace_420565 : CollatzResearch.WordTrace tailWord_420565 prefixEnd_420565 215951991458252271203363 := by
  unfold tailWord_420565
  simp only [CollatzResearch.WordTrace]
  refine ⟨15339265721372306628687149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10226177147581537752458099 15339265721372306628687149)
  ·
    refine ⟨5752224645514614985757681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15339265721372306628687149 5752224645514614985757681)
    ·
      refine ⟨4314168484135961239318261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5752224645514614985757681 4314168484135961239318261)
      ·
        refine ⟨404453295387746366186087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4314168484135961239318261 404453295387746366186087)
        ·
          refine ⟨606679943081619549279131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404453295387746366186087 606679943081619549279131)
          ·
            refine ⟨910019914622429323918697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606679943081619549279131 910019914622429323918697)
            ·
              refine ⟨682514935966821992939023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 910019914622429323918697 682514935966821992939023)
              ·
                refine ⟨1023772403950232989408535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 682514935966821992939023 1023772403950232989408535)
                ·
                  refine ⟨1535658605925349484112803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1023772403950232989408535 1535658605925349484112803)
                  ·
                    refine ⟨2303487908888024226169205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1535658605925349484112803 2303487908888024226169205)
                    ·
                      refine ⟨215951991458252271203363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2303487908888024226169205 215951991458252271203363)
                      ·
                        rfl

theorem cell23_420565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_420565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420565 prefixEnd_420565 := by exact prefixLift 420565
  have htrace : WordTrace (prefixWord ++ tailWord_420565) baseStart_420565 baseEnd_420565 := by
    simpa [prefixWord, tailWord_420565, baseEnd_420565] using wordTrace_append hprefix tailTrace_420565
  have hstable : (prefixWord ++ tailWord_420565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420565).length < 2 ^ (prefixWord ++ tailWord_420565).sum := by decide
  have hdescent : baseEnd_420565 < baseStart_420565 := by decide
  rcases family_descends (prefixWord ++ tailWord_420565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420588 : List Nat := [2, 2, 1, 1, 2, 2, 1, 4, 3, 3, 2]
def baseStart_420588 : Nat := 118140960795 + 420588 * 2 ^ 59
def prefixEnd_420588 : Nat := 4983230072969 + 3 ^ 40 * 420588 * 2
def baseEnd_420588 : Nat := 215963801513305681215757

theorem tailTrace_420588 : CollatzResearch.WordTrace tailWord_420588 prefixEnd_420588 215963801513305681215757 := by
  unfold tailWord_420588
  simp only [CollatzResearch.WordTrace]
  refine ⟨7670052300144490778387209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10226736400192654371182945 7670052300144490778387209)
  ·
    refine ⟨5752539225108368083790407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7670052300144490778387209 5752539225108368083790407)
    ·
      refine ⟨8628808837662552125685611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5752539225108368083790407 8628808837662552125685611)
      ·
        refine ⟨12943213256493828188528417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8628808837662552125685611 12943213256493828188528417)
        ·
          refine ⟨9707409942370371141396313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12943213256493828188528417 9707409942370371141396313)
          ·
            refine ⟨7280557456777778356047235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9707409942370371141396313 7280557456777778356047235)
            ·
              refine ⟨10920836185166667534070853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7280557456777778356047235 10920836185166667534070853)
              ·
                refine ⟨2047656784718750162638285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10920836185166667534070853 2047656784718750162638285)
                ·
                  refine ⟨767871294269531310989357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2047656784718750162638285 767871294269531310989357)
                  ·
                    refine ⟨287951735351074241621009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 767871294269531310989357 287951735351074241621009)
                    ·
                      refine ⟨215963801513305681215757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 287951735351074241621009 215963801513305681215757)
                      ·
                        rfl

theorem cell23_420588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 3, 2].length) (baseStart_420588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420588 prefixEnd_420588 := by exact prefixLift 420588
  have htrace : WordTrace (prefixWord ++ tailWord_420588) baseStart_420588 baseEnd_420588 := by
    simpa [prefixWord, tailWord_420588, baseEnd_420588] using wordTrace_append hprefix tailTrace_420588
  have hstable : (prefixWord ++ tailWord_420588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420588).length < 2 ^ (prefixWord ++ tailWord_420588).sum := by decide
  have hdescent : baseEnd_420588 < baseStart_420588 := by decide
  rcases family_descends (prefixWord ++ tailWord_420588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420596 : List Nat := [2, 6, 1, 1, 3, 1, 1, 2, 1, 1, 4]
def baseStart_420596 : Nat := 118140960795 + 420596 * 2 ^ 59
def prefixEnd_420596 : Nat := 4983230072969 + 3 ^ 40 * 420596 * 2
def baseEnd_420596 : Nat := 215967909358541649915721

theorem tailTrace_420596 : CollatzResearch.WordTrace tailWord_420596 prefixEnd_420596 215967909358541649915721 := by
  unfold tailWord_420596
  simp only [CollatzResearch.WordTrace]
  refine ⟨7670198192129999461532821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10226930922839999282043761 7670198192129999461532821)
  ·
    refine ⟨359540540256093724759351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7670198192129999461532821 359540540256093724759351)
    ·
      refine ⟨539310810384140587139027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359540540256093724759351 539310810384140587139027)
      ·
        refine ⟨808966215576210880708541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 539310810384140587139027 808966215576210880708541)
        ·
          refine ⟨303362330841079080265703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 808966215576210880708541 303362330841079080265703)
          ·
            refine ⟨455043496261618620398555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303362330841079080265703 455043496261618620398555)
            ·
              refine ⟨682565244392427930597833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 455043496261618620398555 682565244392427930597833)
              ·
                refine ⟨511923933294320947948375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 682565244392427930597833 511923933294320947948375)
                ·
                  refine ⟨767885899941481421922563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 511923933294320947948375 767885899941481421922563)
                  ·
                    refine ⟨1151828849912222132883845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 767885899941481421922563 1151828849912222132883845)
                    ·
                      refine ⟨215967909358541649915721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1151828849912222132883845 215967909358541649915721)
                      ·
                        rfl

theorem cell23_420596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_420596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420596 prefixEnd_420596 := by exact prefixLift 420596
  have htrace : WordTrace (prefixWord ++ tailWord_420596) baseStart_420596 baseEnd_420596 := by
    simpa [prefixWord, tailWord_420596, baseEnd_420596] using wordTrace_append hprefix tailTrace_420596
  have hstable : (prefixWord ++ tailWord_420596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420596).length < 2 ^ (prefixWord ++ tailWord_420596).sum := by decide
  have hdescent : baseEnd_420596 < baseStart_420596 := by decide
  rcases family_descends (prefixWord ++ tailWord_420596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420641 : List Nat := [1, 2, 3, 2, 1, 2, 2, 3, 7]
def baseStart_420641 : Nat := 118140960795 + 420641 * 2 ^ 59
def prefixEnd_420641 : Nat := 4983230072969 + 3 ^ 40 * 420641 * 2
def baseEnd_420641 : Nat := 23999001776443774872557

theorem tailTrace_420641 : CollatzResearch.WordTrace tailWord_420641 prefixEnd_420641 23999001776443774872557 := by
  unfold tailWord_420641
  simp only [CollatzResearch.WordTrace]
  refine ⟨15342037669096971608453777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10228025112731314405635851 15342037669096971608453777)
  ·
    refine ⟨11506528251822728706340333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15342037669096971608453777 11506528251822728706340333)
    ·
      refine ⟨4314948094433523264877625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11506528251822728706340333 4314948094433523264877625)
      ·
        refine ⟨3236211070825142448658219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4314948094433523264877625 3236211070825142448658219)
        ·
          refine ⟨4854316606237713672987329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3236211070825142448658219 4854316606237713672987329)
          ·
            refine ⟨3640737454678285254740497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4854316606237713672987329 3640737454678285254740497)
            ·
              refine ⟨2730553091008713941055373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3640737454678285254740497 2730553091008713941055373)
              ·
                refine ⟨1023957409128267727895765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2730553091008713941055373 1023957409128267727895765)
                ·
                  refine ⟨23999001776443774872557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1023957409128267727895765 23999001776443774872557)
                  ·
                    rfl

theorem cell23_420641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 7].length) (baseStart_420641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420641 prefixEnd_420641 := by exact prefixLift 420641
  have htrace : WordTrace (prefixWord ++ tailWord_420641) baseStart_420641 baseEnd_420641 := by
    simpa [prefixWord, tailWord_420641, baseEnd_420641] using wordTrace_append hprefix tailTrace_420641
  have hstable : (prefixWord ++ tailWord_420641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420641).length < 2 ^ (prefixWord ++ tailWord_420641).sum := by decide
  have hdescent : baseEnd_420641 < baseStart_420641 := by decide
  rcases family_descends (prefixWord ++ tailWord_420641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420648 : List Nat := [2, 1, 5, 1, 1, 1, 3, 1, 2, 2, 4]
def baseStart_420648 : Nat := 118140960795 + 420648 * 2 ^ 59
def prefixEnd_420648 : Nat := 4983230072969 + 3 ^ 40 * 420648 * 2
def baseEnd_420648 : Nat := 215994610352575446465481

theorem tailTrace_420648 : CollatzResearch.WordTrace tailWord_420648 prefixEnd_420648 215994610352575446465481 := by
  unfold tailWord_420648
  simp only [CollatzResearch.WordTrace]
  refine ⟨7671146490035805901979299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10228195320047741202639065 7671146490035805901979299)
  ·
    refine ⟨11506719735053708852968949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7671146490035805901979299 11506719735053708852968949)
    ·
      refine ⟨1078754975161285204965839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11506719735053708852968949 1078754975161285204965839)
      ·
        refine ⟨1618132462741927807448759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1078754975161285204965839 1618132462741927807448759)
        ·
          refine ⟨2427198694112891711173139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1618132462741927807448759 2427198694112891711173139)
          ·
            refine ⟨3640798041169337566759709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2427198694112891711173139 3640798041169337566759709)
            ·
              refine ⟨1365299265438501587534891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3640798041169337566759709 1365299265438501587534891)
              ·
                refine ⟨2047948898157752381302337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1365299265438501587534891 2047948898157752381302337)
                ·
                  refine ⟨1535961673618314285976753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2047948898157752381302337 1535961673618314285976753)
                  ·
                    refine ⟨1151971255213735714482565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1535961673618314285976753 1151971255213735714482565)
                    ·
                      refine ⟨215994610352575446465481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1151971255213735714482565 215994610352575446465481)
                      ·
                        rfl

theorem cell23_420648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_420648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420648 prefixEnd_420648 := by exact prefixLift 420648
  have htrace : WordTrace (prefixWord ++ tailWord_420648) baseStart_420648 baseEnd_420648 := by
    simpa [prefixWord, tailWord_420648, baseEnd_420648] using wordTrace_append hprefix tailTrace_420648
  have hstable : (prefixWord ++ tailWord_420648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420648).length < 2 ^ (prefixWord ++ tailWord_420648).sum := by decide
  have hdescent : baseEnd_420648 < baseStart_420648 := by decide
  rcases family_descends (prefixWord ++ tailWord_420648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420651 : List Nat := [1, 1, 1, 1, 2, 1, 2, 5, 1, 5, 3]
def baseStart_420651 : Nat := 118140960795 + 420651 * 2 ^ 59
def prefixEnd_420651 : Nat := 4983230072969 + 3 ^ 40 * 420651 * 2
def baseEnd_420651 : Nat := 215996150794538934727967

theorem tailTrace_420651 : CollatzResearch.WordTrace tailWord_420651 prefixEnd_420651 215996150794538934727967 := by
  unfold tailWord_420651
  simp only [CollatzResearch.WordTrace]
  refine ⟨15342402399060743316317807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10228268266040495544211871 15342402399060743316317807)
  ·
    refine ⟨23013603598591114974476711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15342402399060743316317807 23013603598591114974476711)
    ·
      refine ⟨34520405397886672461715067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23013603598591114974476711 34520405397886672461715067)
      ·
        refine ⟨51780608096830008692572601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34520405397886672461715067 51780608096830008692572601)
        ·
          refine ⟨38835456072622506519429451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51780608096830008692572601 38835456072622506519429451)
          ·
            refine ⟨58253184108933759779144177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38835456072622506519429451 58253184108933759779144177)
            ·
              refine ⟨43689888081700319834358133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58253184108933759779144177 43689888081700319834358133)
              ·
                refine ⟨4095927007659404984471075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43689888081700319834358133 4095927007659404984471075)
                ·
                  refine ⟨6143890511489107476706613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4095927007659404984471075 6143890511489107476706613)
                  ·
                    refine ⟨575989735452103825941245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6143890511489107476706613 575989735452103825941245)
                    ·
                      refine ⟨215996150794538934727967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 575989735452103825941245 215996150794538934727967)
                      ·
                        rfl

theorem cell23_420651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 5, 3].length) (baseStart_420651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420651 prefixEnd_420651 := by exact prefixLift 420651
  have htrace : WordTrace (prefixWord ++ tailWord_420651) baseStart_420651 baseEnd_420651 := by
    simpa [prefixWord, tailWord_420651, baseEnd_420651] using wordTrace_append hprefix tailTrace_420651
  have hstable : (prefixWord ++ tailWord_420651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420651).length < 2 ^ (prefixWord ++ tailWord_420651).sum := by decide
  have hdescent : baseEnd_420651 < baseStart_420651 := by decide
  rcases family_descends (prefixWord ++ tailWord_420651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420673 : List Nat := [1, 2, 5, 3, 2, 1, 2, 1, 1, 3, 2]
def baseStart_420673 : Nat := 118140960795 + 420673 * 2 ^ 59
def prefixEnd_420673 : Nat := 4983230072969 + 3 ^ 40 * 420673 * 2
def baseEnd_420673 : Nat := 216007447368937848652867

theorem tailTrace_420673 : CollatzResearch.WordTrace tailWord_420673 prefixEnd_420673 216007447368937848652867 := by
  unfold tailWord_420673
  simp only [CollatzResearch.WordTrace]
  refine ⟨15343204804981041073618673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10228803203320694049079115 15343204804981041073618673)
  ·
    refine ⟨11507403603735780805214005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15343204804981041073618673 11507403603735780805214005)
    ·
      refine ⟨1078819087850229450488813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11507403603735780805214005 1078819087850229450488813)
      ·
        refine ⟨404557157943836043933305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1078819087850229450488813 404557157943836043933305)
        ·
          refine ⟨303417868457877032949979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 404557157943836043933305 303417868457877032949979)
          ·
            refine ⟨455126802686815549424969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303417868457877032949979 455126802686815549424969)
            ·
              refine ⟨341345102015111662068727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 455126802686815549424969 341345102015111662068727)
              ·
                refine ⟨512017653022667493103091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 341345102015111662068727 512017653022667493103091)
                ·
                  refine ⟨768026479534001239654637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 512017653022667493103091 768026479534001239654637)
                  ·
                    refine ⟨288009929825250464870489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 768026479534001239654637 288009929825250464870489)
                    ·
                      refine ⟨216007447368937848652867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 288009929825250464870489 216007447368937848652867)
                      ·
                        rfl

theorem cell23_420673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_420673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420673 prefixEnd_420673 := by exact prefixLift 420673
  have htrace : WordTrace (prefixWord ++ tailWord_420673) baseStart_420673 baseEnd_420673 := by
    simpa [prefixWord, tailWord_420673, baseEnd_420673] using wordTrace_append hprefix tailTrace_420673
  have hstable : (prefixWord ++ tailWord_420673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420673).length < 2 ^ (prefixWord ++ tailWord_420673).sum := by decide
  have hdescent : baseEnd_420673 < baseStart_420673 := by decide
  rcases family_descends (prefixWord ++ tailWord_420673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420708 : List Nat := [2, 3, 1, 1, 4, 1, 1, 2, 1, 3, 4]
def baseStart_420708 : Nat := 118140960795 + 420708 * 2 ^ 59
def prefixEnd_420708 : Nat := 4983230072969 + 3 ^ 40 * 420708 * 2
def baseEnd_420708 : Nat := 216025419191845211715205

theorem tailTrace_420708 : CollatzResearch.WordTrace tailWord_420708 prefixEnd_420708 216025419191845211715205 := by
  unfold tailWord_420708
  simp only [CollatzResearch.WordTrace]
  refine ⟨7672240679927121025571389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10229654239902828034095185 7672240679927121025571389)
  ·
    refine ⟨2877090254972670384589271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7672240679927121025571389 2877090254972670384589271)
    ·
      refine ⟨4315635382459005576883907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2877090254972670384589271 4315635382459005576883907)
      ·
        refine ⟨6473453073688508365325861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4315635382459005576883907 6473453073688508365325861)
        ·
          refine ⟨1213772451316595318498599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6473453073688508365325861 1213772451316595318498599)
          ·
            refine ⟨1820658676974892977747899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1213772451316595318498599 1820658676974892977747899)
            ·
              refine ⟨2730988015462339466621849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1820658676974892977747899 2730988015462339466621849)
              ·
                refine ⟨2048241011596754599966387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2730988015462339466621849 2048241011596754599966387)
                ·
                  refine ⟨3072361517395131899949581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2048241011596754599966387 3072361517395131899949581)
                  ·
                    refine ⟨1152135569023174462481093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3072361517395131899949581 1152135569023174462481093)
                    ·
                      refine ⟨216025419191845211715205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1152135569023174462481093 216025419191845211715205)
                      ·
                        rfl

theorem cell23_420708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_420708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420708 prefixEnd_420708 := by exact prefixLift 420708
  have htrace : WordTrace (prefixWord ++ tailWord_420708) baseStart_420708 baseEnd_420708 := by
    simpa [prefixWord, tailWord_420708, baseEnd_420708] using wordTrace_append hprefix tailTrace_420708
  have hstable : (prefixWord ++ tailWord_420708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420708).length < 2 ^ (prefixWord ++ tailWord_420708).sum := by decide
  have hdescent : baseEnd_420708 < baseStart_420708 := by decide
  rcases family_descends (prefixWord ++ tailWord_420708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420731 : List Nat := [1, 1, 1, 1, 1, 5, 3, 2, 8]
def baseStart_420731 : Nat := 118140960795 + 420731 * 2 ^ 59
def prefixEnd_420731 : Nat := 4983230072969 + 3 ^ 40 * 420731 * 2
def baseEnd_420731 : Nat := 24004136582988735747511

theorem tailTrace_420731 : CollatzResearch.WordTrace tailWord_420731 prefixEnd_420731 24004136582988735747511 := by
  unfold tailWord_420731
  simp only [CollatzResearch.WordTrace]
  refine ⟨15345320238770916979230047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10230213492513944652820031 15345320238770916979230047)
  ·
    refine ⟨23017980358156375468845071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15345320238770916979230047 23017980358156375468845071)
    ·
      refine ⟨34526970537234563203267607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23017980358156375468845071 34526970537234563203267607)
      ·
        refine ⟨51790455805851844804901411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34526970537234563203267607 51790455805851844804901411)
        ·
          refine ⟨77685683708777767207352117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51790455805851844804901411 77685683708777767207352117)
          ·
            refine ⟨7283032847697915675689261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77685683708777767207352117 7283032847697915675689261)
            ·
              refine ⟨2731137317886718378383473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7283032847697915675689261 2731137317886718378383473)
              ·
                refine ⟨2048352988415038783787605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2731137317886718378383473 2048352988415038783787605)
                ·
                  refine ⟨24004136582988735747511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2048352988415038783787605 24004136582988735747511)
                  ·
                    rfl

theorem cell23_420731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 8].length) (baseStart_420731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420731 prefixEnd_420731 := by exact prefixLift 420731
  have htrace : WordTrace (prefixWord ++ tailWord_420731) baseStart_420731 baseEnd_420731 := by
    simpa [prefixWord, tailWord_420731, baseEnd_420731] using wordTrace_append hprefix tailTrace_420731
  have hstable : (prefixWord ++ tailWord_420731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420731).length < 2 ^ (prefixWord ++ tailWord_420731).sum := by decide
  have hdescent : baseEnd_420731 < baseStart_420731 := by decide
  rcases family_descends (prefixWord ++ tailWord_420731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420745 : List Nat := [1, 2, 1, 1, 5, 3, 1, 2, 2, 2, 3]
def baseStart_420745 : Nat := 118140960795 + 420745 * 2 ^ 59
def prefixEnd_420745 : Nat := 4983230072969 + 3 ^ 40 * 420745 * 2
def baseEnd_420745 : Nat := 216044417976061566952535

theorem tailTrace_420745 : CollatzResearch.WordTrace tailWord_420745 prefixEnd_420745 216044417976061566952535 := by
  unfold tailWord_420745
  simp only [CollatzResearch.WordTrace]
  refine ⟨15345830860720197370239689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10230553907146798246826459 15345830860720197370239689)
  ·
    refine ⟨11509373145540148027679767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15345830860720197370239689 11509373145540148027679767)
    ·
      refine ⟨17264059718310222041519651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11509373145540148027679767 17264059718310222041519651)
      ·
        refine ⟨25896089577465333062279477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17264059718310222041519651 25896089577465333062279477)
        ·
          refine ⟨2427758397887374974588701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25896089577465333062279477 2427758397887374974588701)
          ·
            refine ⟨910409399207765615470763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2427758397887374974588701 910409399207765615470763)
            ·
              refine ⟨1365614098811648423206145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 910409399207765615470763 1365614098811648423206145)
              ·
                refine ⟨1024210574108736317404609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1365614098811648423206145 1024210574108736317404609)
                ·
                  refine ⟨768157930581552238053457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1024210574108736317404609 768157930581552238053457)
                  ·
                    refine ⟨576118447936164178540093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 768157930581552238053457 576118447936164178540093)
                    ·
                      refine ⟨216044417976061566952535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 576118447936164178540093 216044417976061566952535)
                      ·
                        rfl

theorem cell23_420745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 2, 2, 2, 3].length) (baseStart_420745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420745 prefixEnd_420745 := by exact prefixLift 420745
  have htrace : WordTrace (prefixWord ++ tailWord_420745) baseStart_420745 baseEnd_420745 := by
    simpa [prefixWord, tailWord_420745, baseEnd_420745] using wordTrace_append hprefix tailTrace_420745
  have hstable : (prefixWord ++ tailWord_420745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420745).length < 2 ^ (prefixWord ++ tailWord_420745).sum := by decide
  have hdescent : baseEnd_420745 < baseStart_420745 := by decide
  rcases family_descends (prefixWord ++ tailWord_420745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420761 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 2, 9]
def baseStart_420761 : Nat := 118140960795 + 420761 * 2 ^ 59
def prefixEnd_420761 : Nat := 4983230072969 + 3 ^ 40 * 420761 * 2
def baseEnd_420761 : Nat := 72017544555511168117487

theorem tailTrace_420761 : CollatzResearch.WordTrace tailWord_420761 prefixEnd_420761 72017544555511168117487 := by
  unfold tailWord_420761
  simp only [CollatzResearch.WordTrace]
  refine ⟨15346414428662232102822137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10230942952441488068548091 15346414428662232102822137)
  ·
    refine ⟨11509810821496674077116603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15346414428662232102822137 11509810821496674077116603)
    ·
      refine ⟨17264716232245011115674905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11509810821496674077116603 17264716232245011115674905)
      ·
        refine ⟨12948537174183758336756179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17264716232245011115674905 12948537174183758336756179)
        ·
          refine ⟨19422805761275637505134269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12948537174183758336756179 19422805761275637505134269)
          ·
            refine ⟨7283552160478364064425351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19422805761275637505134269 7283552160478364064425351)
            ·
              refine ⟨10925328240717546096638027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7283552160478364064425351 10925328240717546096638027)
              ·
                refine ⟨16387992361076319144957041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10925328240717546096638027 16387992361076319144957041)
                ·
                  refine ⟨12290994270807239358717781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16387992361076319144957041 12290994270807239358717781)
                  ·
                    refine ⟨72017544555511168117487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 12290994270807239358717781 72017544555511168117487)
                    ·
                      rfl

theorem cell23_420761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 9].length) (baseStart_420761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420761 prefixEnd_420761 := by exact prefixLift 420761
  have htrace : WordTrace (prefixWord ++ tailWord_420761) baseStart_420761 baseEnd_420761 := by
    simpa [prefixWord, tailWord_420761, baseEnd_420761] using wordTrace_append hprefix tailTrace_420761
  have hstable : (prefixWord ++ tailWord_420761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420761).length < 2 ^ (prefixWord ++ tailWord_420761).sum := by decide
  have hdescent : baseEnd_420761 < baseStart_420761 := by decide
  rcases family_descends (prefixWord ++ tailWord_420761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420825 : List Nat := [1, 2, 1, 2, 5, 2, 2, 1, 1, 6]
def baseStart_420825 : Nat := 118140960795 + 420825 * 2 ^ 59
def prefixEnd_420825 : Nat := 4983230072969 + 3 ^ 40 * 420825 * 2
def baseEnd_420825 : Nat := 72028498809473751317389

theorem tailTrace_420825 : CollatzResearch.WordTrace tailWord_420825 prefixEnd_420825 72028498809473751317389 := by
  unfold tailWord_420825
  simp only [CollatzResearch.WordTrace]
  refine ⟨15348748700430371033151929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10232499133620247355434619 15348748700430371033151929)
  ·
    refine ⟨11511561525322778274863947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15348748700430371033151929 11511561525322778274863947)
    ·
      refine ⟨17267342287984167412295921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11511561525322778274863947 17267342287984167412295921)
      ·
        refine ⟨12950506715988125559221941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17267342287984167412295921 12950506715988125559221941)
        ·
          refine ⟨1214110004623886771177057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12950506715988125559221941 1214110004623886771177057)
          ·
            refine ⟨910582503467915078382793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1214110004623886771177057 910582503467915078382793)
            ·
              refine ⟨682936877600936308787095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 910582503467915078382793 682936877600936308787095)
              ·
                refine ⟨1024405316401404463180643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 682936877600936308787095 1024405316401404463180643)
                ·
                  refine ⟨1536607974602106694770965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1024405316401404463180643 1536607974602106694770965)
                  ·
                    refine ⟨72028498809473751317389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1536607974602106694770965 72028498809473751317389)
                    ·
                      rfl

theorem cell23_420825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 1, 6].length) (baseStart_420825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420825 prefixEnd_420825 := by exact prefixLift 420825
  have htrace : WordTrace (prefixWord ++ tailWord_420825) baseStart_420825 baseEnd_420825 := by
    simpa [prefixWord, tailWord_420825, baseEnd_420825] using wordTrace_append hprefix tailTrace_420825
  have hstable : (prefixWord ++ tailWord_420825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420825).length < 2 ^ (prefixWord ++ tailWord_420825).sum := by decide
  have hdescent : baseEnd_420825 < baseStart_420825 := by decide
  rcases family_descends (prefixWord ++ tailWord_420825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420835 : List Nat := [1, 1, 1, 6, 1, 1, 1, 3, 3, 2, 3]
def baseStart_420835 : Nat := 118140960795 + 420835 * 2 ^ 59
def prefixEnd_420835 : Nat := 4983230072969 + 3 ^ 40 * 420835 * 2
def baseEnd_420835 : Nat := 216090631234966214827121

theorem tailTrace_420835 : CollatzResearch.WordTrace tailWord_420835 prefixEnd_420835 216090631234966214827121 := by
  unfold tailWord_420835
  simp only [CollatzResearch.WordTrace]
  refine ⟨15349113430394142741015959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10232742286929428494010639 15349113430394142741015959)
  ·
    refine ⟨23023670145591214111523939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15349113430394142741015959 23023670145591214111523939)
    ·
      refine ⟨34535505218386821167285909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23023670145591214111523939 34535505218386821167285909)
      ·
        refine ⟨1618851807111882242216527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34535505218386821167285909 1618851807111882242216527)
        ·
          refine ⟨2428277710667823363324791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1618851807111882242216527 2428277710667823363324791)
          ·
            refine ⟨3642416566001735044987187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2428277710667823363324791 3642416566001735044987187)
            ·
              refine ⟨5463624849002602567480781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3642416566001735044987187 5463624849002602567480781)
              ·
                refine ⟨2048859318375975962805293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5463624849002602567480781 2048859318375975962805293)
                ·
                  refine ⟨768322244390990986051985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2048859318375975962805293 768322244390990986051985)
                  ·
                    refine ⟨576241683293243239538989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 768322244390990986051985 576241683293243239538989)
                    ·
                      refine ⟨216090631234966214827121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 576241683293243239538989 216090631234966214827121)
                      ·
                        rfl

theorem cell23_420835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_420835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420835 prefixEnd_420835 := by exact prefixLift 420835
  have htrace : WordTrace (prefixWord ++ tailWord_420835) baseStart_420835 baseEnd_420835 := by
    simpa [prefixWord, tailWord_420835, baseEnd_420835] using wordTrace_append hprefix tailTrace_420835
  have hstable : (prefixWord ++ tailWord_420835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420835).length < 2 ^ (prefixWord ++ tailWord_420835).sum := by decide
  have hdescent : baseEnd_420835 < baseStart_420835 := by decide
  rcases family_descends (prefixWord ++ tailWord_420835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420846 : List Nat := [4, 1, 2, 1, 5, 1, 2, 1, 1, 5]
def baseStart_420846 : Nat := 118140960795 + 420846 * 2 ^ 59
def prefixEnd_420846 : Nat := 4983230072969 + 3 ^ 40 * 420846 * 2
def baseEnd_420846 : Nat := 72032093174055223929857

theorem tailTrace_420846 : CollatzResearch.WordTrace tailWord_420846 prefixEnd_420846 72032093174055223929857 := by
  unfold tailWord_420846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1918689329169286452458299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10233009755569527746444261 1918689329169286452458299)
  ·
    refine ⟨2878033993753929678687449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1918689329169286452458299 2878033993753929678687449)
    ·
      refine ⟨2158525495315447259015587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2878033993753929678687449 2158525495315447259015587)
      ·
        refine ⟨3237788242973170888523381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2158525495315447259015587 3237788242973170888523381)
        ·
          refine ⟨303542647778734770799067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3237788242973170888523381 303542647778734770799067)
          ·
            refine ⟨455313971668102156198601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303542647778734770799067 455313971668102156198601)
            ·
              refine ⟨341485478751076617148951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 455313971668102156198601 341485478751076617148951)
              ·
                refine ⟨512228218126614925723427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 341485478751076617148951 512228218126614925723427)
                ·
                  refine ⟨768342327189922388585141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 512228218126614925723427 768342327189922388585141)
                  ·
                    refine ⟨72032093174055223929857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 768342327189922388585141 72032093174055223929857)
                    ·
                      rfl

theorem cell23_420846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_420846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420846 prefixEnd_420846 := by exact prefixLift 420846
  have htrace : WordTrace (prefixWord ++ tailWord_420846) baseStart_420846 baseEnd_420846 := by
    simpa [prefixWord, tailWord_420846, baseEnd_420846] using wordTrace_append hprefix tailTrace_420846
  have hstable : (prefixWord ++ tailWord_420846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420846).length < 2 ^ (prefixWord ++ tailWord_420846).sum := by decide
  have hdescent : baseEnd_420846 < baseStart_420846 := by decide
  rcases family_descends (prefixWord ++ tailWord_420846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420849 : List Nat := [1, 2, 2, 2, 4, 3, 2, 1, 1, 1, 4]
def baseStart_420849 : Nat := 118140960795 + 420849 * 2 ^ 59
def prefixEnd_420849 : Nat := 4983230072969 + 3 ^ 40 * 420849 * 2
def baseEnd_420849 : Nat := 216097819964129160052057

theorem tailTrace_420849 : CollatzResearch.WordTrace tailWord_420849 prefixEnd_420849 216097819964129160052057 := by
  unfold tailWord_420849
  simp only [CollatzResearch.WordTrace]
  refine ⟨15349624052343423132025601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10233082701562282088017067 15349624052343423132025601)
  ·
    refine ⟨11512218039257567349019201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15349624052343423132025601 11512218039257567349019201)
    ·
      refine ⟨8634163529443175511764401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11512218039257567349019201 8634163529443175511764401)
      ·
        refine ⟨6475622647082381633823301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8634163529443175511764401 6475622647082381633823301)
        ·
          refine ⟨1214179246327946556341869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6475622647082381633823301 1214179246327946556341869)
          ·
            refine ⟨455317217372979958628201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1214179246327946556341869 455317217372979958628201)
            ·
              refine ⟨341487913029734968971151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 455317217372979958628201 341487913029734968971151)
              ·
                refine ⟨512231869544602453456727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 341487913029734968971151 512231869544602453456727)
                ·
                  refine ⟨768347804316903680185091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 512231869544602453456727 768347804316903680185091)
                  ·
                    refine ⟨1152521706475355520277637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 768347804316903680185091 1152521706475355520277637)
                    ·
                      refine ⟨216097819964129160052057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1152521706475355520277637 216097819964129160052057)
                      ·
                        rfl

theorem cell23_420849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 1, 1, 4].length) (baseStart_420849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420849 prefixEnd_420849 := by exact prefixLift 420849
  have htrace : WordTrace (prefixWord ++ tailWord_420849) baseStart_420849 baseEnd_420849 := by
    simpa [prefixWord, tailWord_420849, baseEnd_420849] using wordTrace_append hprefix tailTrace_420849
  have hstable : (prefixWord ++ tailWord_420849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420849).length < 2 ^ (prefixWord ++ tailWord_420849).sum := by decide
  have hdescent : baseEnd_420849 < baseStart_420849 := by decide
  rcases family_descends (prefixWord ++ tailWord_420849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420975 : List Nat := [1, 1, 2, 1, 3, 3, 1, 4, 2, 5]
def baseStart_420975 : Nat := 118140960795 + 420975 * 2 ^ 59
def prefixEnd_420975 : Nat := 4983230072969 + 3 ^ 40 * 420975 * 2
def baseEnd_420975 : Nat := 72054172842198555692159

theorem tailTrace_420975 : CollatzResearch.WordTrace tailWord_420975 prefixEnd_420975 72054172842198555692159 := by
  unfold tailWord_420975
  simp only [CollatzResearch.WordTrace]
  refine ⟨15354219649886946651112379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10236146433257964434074919 15354219649886946651112379)
  ·
    refine ⟨23031329474830419976668569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15354219649886946651112379 23031329474830419976668569)
    ·
      refine ⟨17273497106122814982501427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23031329474830419976668569 17273497106122814982501427)
      ·
        refine ⟨25910245659184222473752141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17273497106122814982501427 25910245659184222473752141)
        ·
          refine ⟨9716342122194083427657053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25910245659184222473752141 9716342122194083427657053)
          ·
            refine ⟨3643628295822781285371395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9716342122194083427657053 3643628295822781285371395)
            ·
              refine ⟨5465442443734171928057093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3643628295822781285371395 5465442443734171928057093)
              ·
                refine ⟨1024770458200157236510705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5465442443734171928057093 1024770458200157236510705)
                ·
                  refine ⟨768577843650117927383029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1024770458200157236510705 768577843650117927383029)
                  ·
                    refine ⟨72054172842198555692159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 768577843650117927383029 72054172842198555692159)
                    ·
                      rfl

theorem cell23_420975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 5].length) (baseStart_420975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420975 prefixEnd_420975 := by exact prefixLift 420975
  have htrace : WordTrace (prefixWord ++ tailWord_420975) baseStart_420975 baseEnd_420975 := by
    simpa [prefixWord, tailWord_420975, baseEnd_420975] using wordTrace_append hprefix tailTrace_420975
  have hstable : (prefixWord ++ tailWord_420975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420975).length < 2 ^ (prefixWord ++ tailWord_420975).sum := by decide
  have hdescent : baseEnd_420975 < baseStart_420975 := by decide
  rcases family_descends (prefixWord ++ tailWord_420975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420990 : List Nat := [4, 2, 4, 1, 1, 1, 2, 1, 1, 4, 2]
def baseStart_420990 : Nat := 118140960795 + 420990 * 2 ^ 59
def prefixEnd_420990 : Nat := 4983230072969 + 3 ^ 40 * 420990 * 2
def baseEnd_420990 : Nat := 216170220736413108388909

theorem tailTrace_420990 : CollatzResearch.WordTrace tailWord_420990 prefixEnd_420990 216170220736413108388909 := by
  unfold tailWord_420990
  simp only [CollatzResearch.WordTrace]
  refine ⟨1919345843104075526613553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10236511163221736141938949 1919345843104075526613553)
  ·
    refine ⟨1439509382328056644960165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1919345843104075526613553 1439509382328056644960165)
    ·
      refine ⟨269908009186510620930031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1439509382328056644960165 269908009186510620930031)
      ·
        refine ⟨404862013779765931395047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269908009186510620930031 404862013779765931395047)
        ·
          refine ⟨607293020669648897092571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404862013779765931395047 607293020669648897092571)
          ·
            refine ⟨910939531004473345638857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 607293020669648897092571 910939531004473345638857)
            ·
              refine ⟨683204648253355009229143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 910939531004473345638857 683204648253355009229143)
              ·
                refine ⟨1024806972380032513843715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 683204648253355009229143 1024806972380032513843715)
                ·
                  refine ⟨1537210458570048770765573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1024806972380032513843715 1537210458570048770765573)
                  ·
                    refine ⟨288226960981884144518545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1537210458570048770765573 288226960981884144518545)
                    ·
                      refine ⟨216170220736413108388909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 288226960981884144518545 216170220736413108388909)
                      ·
                        rfl

theorem cell23_420990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_420990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420990 prefixEnd_420990 := by exact prefixLift 420990
  have htrace : WordTrace (prefixWord ++ tailWord_420990) baseStart_420990 baseEnd_420990 := by
    simpa [prefixWord, tailWord_420990, baseEnd_420990] using wordTrace_append hprefix tailTrace_420990
  have hstable : (prefixWord ++ tailWord_420990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420990).length < 2 ^ (prefixWord ++ tailWord_420990).sum := by decide
  have hdescent : baseEnd_420990 < baseStart_420990 := by decide
  rcases family_descends (prefixWord ++ tailWord_420990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420995 : List Nat := [1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 4]
def baseStart_420995 : Nat := 118140960795 + 420995 * 2 ^ 59
def prefixEnd_420995 : Nat := 4983230072969 + 3 ^ 40 * 420995 * 2
def baseEnd_420995 : Nat := 216172788139685588826385

theorem tailTrace_420995 : CollatzResearch.WordTrace tailWord_420995 prefixEnd_420995 216172788139685588826385 := by
  unfold tailWord_420995
  simp only [CollatzResearch.WordTrace]
  refine ⟨15354949109814490066840439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10236632739876326711226959 15354949109814490066840439)
  ·
    refine ⟨23032423664721735100260659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15354949109814490066840439 23032423664721735100260659)
    ·
      refine ⟨34548635497082602650390989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23032423664721735100260659 34548635497082602650390989)
      ·
        refine ⟨12955738311405975993896621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34548635497082602650390989 12955738311405975993896621)
        ·
          refine ⟨4858401866777240997711233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12955738311405975993896621 4858401866777240997711233)
          ·
            refine ⟨3643801400082930748283425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4858401866777240997711233 3643801400082930748283425)
            ·
              refine ⟨2732851050062198061212569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3643801400082930748283425 2732851050062198061212569)
              ·
                refine ⟨2049638287546648545909427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2732851050062198061212569 2049638287546648545909427)
                ·
                  refine ⟨3074457431319972818864141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2049638287546648545909427 3074457431319972818864141)
                  ·
                    refine ⟨1152921536744989807074053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3074457431319972818864141 1152921536744989807074053)
                    ·
                      refine ⟨216172788139685588826385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1152921536744989807074053 216172788139685588826385)
                      ·
                        rfl

theorem cell23_420995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 4].length) (baseStart_420995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_420995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_420995 prefixEnd_420995 := by exact prefixLift 420995
  have htrace : WordTrace (prefixWord ++ tailWord_420995) baseStart_420995 baseEnd_420995 := by
    simpa [prefixWord, tailWord_420995, baseEnd_420995] using wordTrace_append hprefix tailTrace_420995
  have hstable : (prefixWord ++ tailWord_420995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420995).length < 2 ^ (prefixWord ++ tailWord_420995).sum := by decide
  have hdescent : baseEnd_420995 < baseStart_420995 := by decide
  rcases family_descends (prefixWord ++ tailWord_420995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421025 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 1, 3, 6]
def baseStart_421025 : Nat := 118140960795 + 421025 * 2 ^ 59
def prefixEnd_421025 : Nat := 4983230072969 + 3 ^ 40 * 421025 * 2
def baseEnd_421025 : Nat := 216188192559320471451247

theorem tailTrace_421025 : CollatzResearch.WordTrace tailWord_421025 prefixEnd_421025 216188192559320471451247 := by
  unfold tailWord_421025
  simp only [CollatzResearch.WordTrace]
  refine ⟨15356043299705805190432529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10237362199803870126955019 15356043299705805190432529)
  ·
    refine ⟨11517032474779353892824397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15356043299705805190432529 11517032474779353892824397)
    ·
      refine ⟨4318887178042257709809149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11517032474779353892824397 4318887178042257709809149)
      ·
        refine ⟨1619582691765846641178431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4318887178042257709809149 1619582691765846641178431)
        ·
          refine ⟨2429374037648769961767647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1619582691765846641178431 2429374037648769961767647)
          ·
            refine ⟨3644061056473154942651471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2429374037648769961767647 3644061056473154942651471)
            ·
              refine ⟨5466091584709732413977207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3644061056473154942651471 5466091584709732413977207)
              ·
                refine ⟨8199137377064598620965811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5466091584709732413977207 8199137377064598620965811)
                ·
                  refine ⟨12298706065596897931448717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8199137377064598620965811 12298706065596897931448717)
                  ·
                    refine ⟨4612014774598836724293269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12298706065596897931448717 4612014774598836724293269)
                    ·
                      refine ⟨216188192559320471451247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4612014774598836724293269 216188192559320471451247)
                      ·
                        rfl

theorem cell23_421025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_421025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421025 prefixEnd_421025 := by exact prefixLift 421025
  have htrace : WordTrace (prefixWord ++ tailWord_421025) baseStart_421025 baseEnd_421025 := by
    simpa [prefixWord, tailWord_421025, baseEnd_421025] using wordTrace_append hprefix tailTrace_421025
  have hstable : (prefixWord ++ tailWord_421025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421025).length < 2 ^ (prefixWord ++ tailWord_421025).sum := by decide
  have hdescent : baseEnd_421025 < baseStart_421025 := by decide
  rcases family_descends (prefixWord ++ tailWord_421025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421039 : List Nat := [1, 1, 2, 1, 2, 3, 4, 4, 1, 4]
def baseStart_421039 : Nat := 118140960795 + 421039 * 2 ^ 59
def prefixEnd_421039 : Nat := 4983230072969 + 3 ^ 40 * 421039 * 2
def baseEnd_421039 : Nat := 72065127096161138892061

theorem tailTrace_421039 : CollatzResearch.WordTrace tailWord_421039 prefixEnd_421039 72065127096161138892061 := by
  unfold tailWord_421039
  simp only [CollatzResearch.WordTrace]
  refine ⟨15356553921655085581442171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10237702614436723720961447 15356553921655085581442171)
  ·
    refine ⟨23034830882482628372163257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15356553921655085581442171 23034830882482628372163257)
    ·
      refine ⟨17276123161861971279122443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23034830882482628372163257 17276123161861971279122443)
      ·
        refine ⟨25914184742792956918683665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17276123161861971279122443 25914184742792956918683665)
        ·
          refine ⟨19435638557094717689012749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25914184742792956918683665 19435638557094717689012749)
          ·
            refine ⟨7288364458910519133379781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19435638557094717689012749 7288364458910519133379781)
            ·
              refine ⟨1366568336045722337508709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7288364458910519133379781 1366568336045722337508709)
              ·
                refine ⟨256231563008572938282883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1366568336045722337508709 256231563008572938282883)
                ·
                  refine ⟨384347344512859407424325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 256231563008572938282883 384347344512859407424325)
                  ·
                    refine ⟨72065127096161138892061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 384347344512859407424325 72065127096161138892061)
                    ·
                      rfl

theorem cell23_421039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 4, 1, 4].length) (baseStart_421039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421039 prefixEnd_421039 := by exact prefixLift 421039
  have htrace : WordTrace (prefixWord ++ tailWord_421039) baseStart_421039 baseEnd_421039 := by
    simpa [prefixWord, tailWord_421039, baseEnd_421039] using wordTrace_append hprefix tailTrace_421039
  have hstable : (prefixWord ++ tailWord_421039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421039).length < 2 ^ (prefixWord ++ tailWord_421039).sum := by decide
  have hdescent : baseEnd_421039 < baseStart_421039 := by decide
  rcases family_descends (prefixWord ++ tailWord_421039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421065 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 7, 5]
def baseStart_421065 : Nat := 118140960795 + 421065 * 2 ^ 59
def prefixEnd_421065 : Nat := 4983230072969 + 3 ^ 40 * 421065 * 2
def baseEnd_421065 : Nat := 72069577261833438317021

theorem tailTrace_421065 : CollatzResearch.WordTrace tailWord_421065 prefixEnd_421065 72069577261833438317021 := by
  unfold tailWord_421065
  simp only [CollatzResearch.WordTrace]
  refine ⟨15357502219560892021888649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10238334813040594681259099 15357502219560892021888649)
  ·
    refine ⟨11518126664670669016416487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15357502219560892021888649 11518126664670669016416487)
    ·
      refine ⟨17277189997006003524624731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11518126664670669016416487 17277189997006003524624731)
      ·
        refine ⟨25915784995509005286937097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17277189997006003524624731 25915784995509005286937097)
        ·
          refine ⟨19436838746631753965202823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25915784995509005286937097 19436838746631753965202823)
          ·
            refine ⟨29155258119947630947804235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19436838746631753965202823 29155258119947630947804235)
            ·
              refine ⟨43732887179921446421706353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29155258119947630947804235 43732887179921446421706353)
              ·
                refine ⟨32799665384941084816279765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43732887179921446421706353 32799665384941084816279765)
                ·
                  refine ⟨768742157459556675381557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 32799665384941084816279765 768742157459556675381557)
                  ·
                    refine ⟨72069577261833438317021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 768742157459556675381557 72069577261833438317021)
                    ·
                      rfl

theorem cell23_421065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 7, 5].length) (baseStart_421065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421065 prefixEnd_421065 := by exact prefixLift 421065
  have htrace : WordTrace (prefixWord ++ tailWord_421065) baseStart_421065 baseEnd_421065 := by
    simpa [prefixWord, tailWord_421065, baseEnd_421065] using wordTrace_append hprefix tailTrace_421065
  have hstable : (prefixWord ++ tailWord_421065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421065).length < 2 ^ (prefixWord ++ tailWord_421065).sum := by decide
  have hdescent : baseEnd_421065 < baseStart_421065 := by decide
  rcases family_descends (prefixWord ++ tailWord_421065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421089 : List Nat := [1, 2, 3, 1, 3, 2, 1, 1, 4, 3, 2]
def baseStart_421089 : Nat := 118140960795 + 421089 * 2 ^ 59
def prefixEnd_421089 : Nat := 4983230072969 + 3 ^ 40 * 421089 * 2
def baseEnd_421089 : Nat := 216221055321208221050953

theorem tailTrace_421089 : CollatzResearch.WordTrace tailWord_421089 prefixEnd_421089 216221055321208221050953 := by
  unfold tailWord_421089
  simp only [CollatzResearch.WordTrace]
  refine ⟨15358377571473944120762321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10238918380982629413841547 15358377571473944120762321)
  ·
    refine ⟨11518783178605458090571741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15358377571473944120762321 11518783178605458090571741)
    ·
      refine ⟨4319543691977046783964403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11518783178605458090571741 4319543691977046783964403)
      ·
        refine ⟨6479315537965570175946605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4319543691977046783964403 6479315537965570175946605)
        ·
          refine ⟨2429743326737088815979977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6479315537965570175946605 2429743326737088815979977)
          ·
            refine ⟨1822307495052816611984983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2429743326737088815979977 1822307495052816611984983)
            ·
              refine ⟨2733461242579224917977475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1822307495052816611984983 2733461242579224917977475)
              ·
                refine ⟨4100191863868837376966213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2733461242579224917977475 4100191863868837376966213)
                ·
                  refine ⟨768785974475407008181165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4100191863868837376966213 768785974475407008181165)
                  ·
                    refine ⟨288294740428277628067937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 768785974475407008181165 288294740428277628067937)
                    ·
                      refine ⟨216221055321208221050953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 288294740428277628067937 216221055321208221050953)
                      ·
                        rfl

theorem cell23_421089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 3, 2].length) (baseStart_421089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421089 prefixEnd_421089 := by exact prefixLift 421089
  have htrace : WordTrace (prefixWord ++ tailWord_421089) baseStart_421089 baseEnd_421089 := by
    simpa [prefixWord, tailWord_421089, baseEnd_421089] using wordTrace_append hprefix tailTrace_421089
  have hstable : (prefixWord ++ tailWord_421089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421089).length < 2 ^ (prefixWord ++ tailWord_421089).sum := by decide
  have hdescent : baseEnd_421089 < baseStart_421089 := by decide
  rcases family_descends (prefixWord ++ tailWord_421089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421116 : List Nat := [2, 2, 2, 1, 5, 2, 1, 2, 1, 5]
def baseStart_421116 : Nat := 118140960795 + 421116 * 2 ^ 59
def prefixEnd_421116 : Nat := 4983230072969 + 3 ^ 40 * 421116 * 2
def baseEnd_421116 : Nat := 72078306432959871804443

theorem tailTrace_421116 : CollatzResearch.WordTrace tailWord_421116 prefixEnd_421116 72078306432959871804443 := by
  unfold tailWord_421116
  simp only [CollatzResearch.WordTrace]
  refine ⟨7679681171188063865997601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10239574894917418487996801 7679681171188063865997601)
  ·
    refine ⟨5759760878391047899498201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7679681171188063865997601 5759760878391047899498201)
    ·
      refine ⟨4319820658793285924623651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5759760878391047899498201 4319820658793285924623651)
      ·
        refine ⟨6479730988189928886935477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4319820658793285924623651 6479730988189928886935477)
        ·
          refine ⟨607474780142805833150201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6479730988189928886935477 607474780142805833150201)
          ·
            refine ⟨455606085107104374862651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 607474780142805833150201 455606085107104374862651)
            ·
              refine ⟨683409127660656562293977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 455606085107104374862651 683409127660656562293977)
              ·
                refine ⟨512556845745492421720483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 683409127660656562293977 512556845745492421720483)
                ·
                  refine ⟨768835268618238632580725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 512556845745492421720483 768835268618238632580725)
                  ·
                    refine ⟨72078306432959871804443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 768835268618238632580725 72078306432959871804443)
                    ·
                      rfl

theorem cell23_421116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 1, 5].length) (baseStart_421116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421116 prefixEnd_421116 := by exact prefixLift 421116
  have htrace : WordTrace (prefixWord ++ tailWord_421116) baseStart_421116 baseEnd_421116 := by
    simpa [prefixWord, tailWord_421116, baseEnd_421116] using wordTrace_append hprefix tailTrace_421116
  have hstable : (prefixWord ++ tailWord_421116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421116).length < 2 ^ (prefixWord ++ tailWord_421116).sum := by decide
  have hdescent : baseEnd_421116 < baseStart_421116 := by decide
  rcases family_descends (prefixWord ++ tailWord_421116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421119 : List Nat := [1, 1, 2, 2, 1, 5, 3, 2, 1, 1, 4]
def baseStart_421119 : Nat := 118140960795 + 421119 * 2 ^ 59
def prefixEnd_421119 : Nat := 4983230072969 + 3 ^ 40 * 421119 * 2
def baseEnd_421119 : Nat := 216236459740843103675815

theorem tailTrace_421119 : CollatzResearch.WordTrace tailWord_421119 prefixEnd_421119 216236459740843103675815 := by
  unfold tailWord_421119
  simp only [CollatzResearch.WordTrace]
  refine ⟨15359471761365259244354411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10239647840910172829569607 15359471761365259244354411)
  ·
    refine ⟨23039207642047888866531617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15359471761365259244354411 23039207642047888866531617)
    ·
      refine ⟨17279405731535916649898713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23039207642047888866531617 17279405731535916649898713)
      ·
        refine ⟨12959554298651937487424035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17279405731535916649898713 12959554298651937487424035)
        ·
          refine ⟨19439331447977906231136053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12959554298651937487424035 19439331447977906231136053)
          ·
            refine ⟨1822437323247928709169005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19439331447977906231136053 1822437323247928709169005)
            ·
              refine ⟨683413996217973265938377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1822437323247928709169005 683413996217973265938377)
              ·
                refine ⟨512560497163479949453783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 683413996217973265938377 512560497163479949453783)
                ·
                  refine ⟨768840745745219924180675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 512560497163479949453783 768840745745219924180675)
                  ·
                    refine ⟨1153261118617829886271013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 768840745745219924180675 1153261118617829886271013)
                    ·
                      refine ⟨216236459740843103675815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1153261118617829886271013 216236459740843103675815)
                      ·
                        rfl

theorem cell23_421119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 1, 4].length) (baseStart_421119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421119 prefixEnd_421119 := by exact prefixLift 421119
  have htrace : WordTrace (prefixWord ++ tailWord_421119) baseStart_421119 baseEnd_421119 := by
    simpa [prefixWord, tailWord_421119, baseEnd_421119] using wordTrace_append hprefix tailTrace_421119
  have hstable : (prefixWord ++ tailWord_421119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421119).length < 2 ^ (prefixWord ++ tailWord_421119).sum := by decide
  have hdescent : baseEnd_421119 < baseStart_421119 := by decide
  rcases family_descends (prefixWord ++ tailWord_421119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421125 : List Nat := [1, 3, 1, 1, 2, 1, 3, 11]
def baseStart_421125 : Nat := 118140960795 + 421125 * 2 ^ 59
def prefixEnd_421125 : Nat := 4983230072969 + 3 ^ 40 * 421125 * 2
def baseEnd_421125 : Nat := 8008871874991484451881

theorem tailTrace_421125 : CollatzResearch.WordTrace tailWord_421125 prefixEnd_421125 8008871874991484451881 := by
  unfold tailWord_421125
  simp only [CollatzResearch.WordTrace]
  refine ⟨15359690599343522269072829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10239793732895681512715219 15359690599343522269072829)
  ·
    refine ⟨5759883974753820850902311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15359690599343522269072829 5759883974753820850902311)
    ·
      refine ⟨8639825962130731276353467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5759883974753820850902311 8639825962130731276353467)
      ·
        refine ⟨12959738943196096914530201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8639825962130731276353467 12959738943196096914530201)
        ·
          refine ⟨9719804207397072685897651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12959738943196096914530201 9719804207397072685897651)
          ·
            refine ⟨14579706311095609028846477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9719804207397072685897651 14579706311095609028846477)
            ·
              refine ⟨5467389866660853385817429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14579706311095609028846477 5467389866660853385817429)
              ·
                refine ⟨8008871874991484451881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 5467389866660853385817429 8008871874991484451881)
                ·
                  rfl

theorem cell23_421125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 11].length) (baseStart_421125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421125 prefixEnd_421125 := by exact prefixLift 421125
  have htrace : WordTrace (prefixWord ++ tailWord_421125) baseStart_421125 baseEnd_421125 := by
    simpa [prefixWord, tailWord_421125, baseEnd_421125] using wordTrace_append hprefix tailTrace_421125
  have hstable : (prefixWord ++ tailWord_421125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421125).length < 2 ^ (prefixWord ++ tailWord_421125).sum := by decide
  have hdescent : baseEnd_421125 < baseStart_421125 := by decide
  rcases family_descends (prefixWord ++ tailWord_421125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421132 : List Nat := [2, 2, 1, 2, 2, 3, 1, 1, 3, 2, 4]
def baseStart_421132 : Nat := 118140960795 + 421132 * 2 ^ 59
def prefixEnd_421132 : Nat := 4983230072969 + 3 ^ 40 * 421132 * 2
def baseEnd_421132 : Nat := 216243134989351552813255

theorem tailTrace_421132 : CollatzResearch.WordTrace tailWord_421132 prefixEnd_421132 216243134989351552813255 := by
  unfold tailWord_421132
  simp only [CollatzResearch.WordTrace]
  refine ⟨7679972955159081232288825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10239963940212108309718433 7679972955159081232288825)
  ·
    refine ⟨5759979716369310924216619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7679972955159081232288825 5759979716369310924216619)
    ·
      refine ⟨8639969574553966386324929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5759979716369310924216619 8639969574553966386324929)
      ·
        refine ⟨6479977180915474789743697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8639969574553966386324929 6479977180915474789743697)
        ·
          refine ⟨4859982885686606092307773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6479977180915474789743697 4859982885686606092307773)
          ·
            refine ⟨1822493582132477284615415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4859982885686606092307773 1822493582132477284615415)
            ·
              refine ⟨2733740373198715926923123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1822493582132477284615415 2733740373198715926923123)
              ·
                refine ⟨4100610559798073890384685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2733740373198715926923123 4100610559798073890384685)
                ·
                  refine ⟨1537728959924277708894257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4100610559798073890384685 1537728959924277708894257)
                  ·
                    refine ⟨1153296719943208281670693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1537728959924277708894257 1153296719943208281670693)
                    ·
                      refine ⟨216243134989351552813255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1153296719943208281670693 216243134989351552813255)
                      ·
                        rfl

theorem cell23_421132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_421132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421132 prefixEnd_421132 := by exact prefixLift 421132
  have htrace : WordTrace (prefixWord ++ tailWord_421132) baseStart_421132 baseEnd_421132 := by
    simpa [prefixWord, tailWord_421132, baseEnd_421132] using wordTrace_append hprefix tailTrace_421132
  have hstable : (prefixWord ++ tailWord_421132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421132).length < 2 ^ (prefixWord ++ tailWord_421132).sum := by decide
  have hdescent : baseEnd_421132 < baseStart_421132 := by decide
  rcases family_descends (prefixWord ++ tailWord_421132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421145 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 2, 3, 8]
def baseStart_421145 : Nat := 118140960795 + 421145 * 2 ^ 59
def prefixEnd_421145 : Nat := 4983230072969 + 3 ^ 40 * 421145 * 2
def baseEnd_421145 : Nat := 216249810237860001950695

theorem tailTrace_421145 : CollatzResearch.WordTrace tailWord_421145 prefixEnd_421145 216249810237860001950695 := by
  unfold tailWord_421145
  simp only [CollatzResearch.WordTrace]
  refine ⟨15360420059271065684800889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10240280039514043789867259 15360420059271065684800889)
  ·
    refine ⟨11520315044453299263600667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15360420059271065684800889 11520315044453299263600667)
    ·
      refine ⟨17280472566679948895401001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11520315044453299263600667 17280472566679948895401001)
      ·
        refine ⟨12960354425009961671550751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17280472566679948895401001 12960354425009961671550751)
        ·
          refine ⟨19440531637514942507326127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12960354425009961671550751 19440531637514942507326127)
          ·
            refine ⟨29160797456272413760989191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19440531637514942507326127 29160797456272413760989191)
            ·
              refine ⟨43741196184408620641483787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29160797456272413760989191 43741196184408620641483787)
              ·
                refine ⟨65611794276612930962225681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43741196184408620641483787 65611794276612930962225681)
                ·
                  refine ⟨49208845707459698221669261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65611794276612930962225681 49208845707459698221669261)
                  ·
                    refine ⟨18453317140297386833125973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49208845707459698221669261 18453317140297386833125973)
                    ·
                      refine ⟨216249810237860001950695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 18453317140297386833125973 216249810237860001950695)
                      ·
                        rfl

theorem cell23_421145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_421145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421145 prefixEnd_421145 := by exact prefixLift 421145
  have htrace : WordTrace (prefixWord ++ tailWord_421145) baseStart_421145 baseEnd_421145 := by
    simpa [prefixWord, tailWord_421145, baseEnd_421145] using wordTrace_append hprefix tailTrace_421145
  have hstable : (prefixWord ++ tailWord_421145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421145).length < 2 ^ (prefixWord ++ tailWord_421145).sum := by decide
  have hdescent : baseEnd_421145 < baseStart_421145 := by decide
  rcases family_descends (prefixWord ++ tailWord_421145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421146 : List Nat := [3, 1, 1, 3, 3, 2, 2, 2, 2, 4]
def baseStart_421146 : Nat := 118140960795 + 421146 * 2 ^ 59
def prefixEnd_421146 : Nat := 4983230072969 + 3 ^ 40 * 421146 * 2
def baseEnd_421146 : Nat := 72083441239504832679397

theorem tailTrace_421146 : CollatzResearch.WordTrace tailWord_421146 prefixEnd_421146 72083441239504832679397 := by
  unfold tailWord_421146
  simp only [CollatzResearch.WordTrace]
  refine ⟨3840114133066860713896823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10240304354844961903724861 3840114133066860713896823)
  ·
    refine ⟨5760171199600291070845235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3840114133066860713896823 5760171199600291070845235)
    ·
      refine ⟨8640256799400436606267853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5760171199600291070845235 8640256799400436606267853)
      ·
        refine ⟨3240096299775163727350445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8640256799400436606267853 3240096299775163727350445)
        ·
          refine ⟨1215036112415686397756417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3240096299775163727350445 1215036112415686397756417)
          ·
            refine ⟨911277084311764798317313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1215036112415686397756417 911277084311764798317313)
            ·
              refine ⟨683457813233823598737985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 911277084311764798317313 683457813233823598737985)
              ·
                refine ⟨512593359925367699053489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 683457813233823598737985 512593359925367699053489)
                ·
                  refine ⟨384445019944025774290117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 512593359925367699053489 384445019944025774290117)
                  ·
                    refine ⟨72083441239504832679397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 384445019944025774290117 72083441239504832679397)
                    ·
                      rfl

theorem cell23_421146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 2, 4].length) (baseStart_421146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421146 prefixEnd_421146 := by exact prefixLift 421146
  have htrace : WordTrace (prefixWord ++ tailWord_421146) baseStart_421146 baseEnd_421146 := by
    simpa [prefixWord, tailWord_421146, baseEnd_421146] using wordTrace_append hprefix tailTrace_421146
  have hstable : (prefixWord ++ tailWord_421146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421146).length < 2 ^ (prefixWord ++ tailWord_421146).sum := by decide
  have hdescent : baseEnd_421146 < baseStart_421146 := by decide
  rcases family_descends (prefixWord ++ tailWord_421146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421169 : List Nat := [1, 2, 2, 3, 3, 1, 1, 3, 1, 3, 3]
def baseStart_421169 : Nat := 118140960795 + 421169 * 2 ^ 59
def prefixEnd_421169 : Nat := 4983230072969 + 3 ^ 40 * 421169 * 2
def baseEnd_421169 : Nat := 216262133773567908050585

theorem tailTrace_421169 : CollatzResearch.WordTrace tailWord_421169 prefixEnd_421169 216262133773567908050585 := by
  unfold tailWord_421169
  simp only [CollatzResearch.WordTrace]
  refine ⟨15361295411184117783674561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10240863607456078522449707 15361295411184117783674561)
  ·
    refine ⟨11520971558388088337755921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15361295411184117783674561 11520971558388088337755921)
    ·
      refine ⟨8640728668791066253316941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11520971558388088337755921 8640728668791066253316941)
      ·
        refine ⟨3240273250796649844993853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8640728668791066253316941 3240273250796649844993853)
        ·
          refine ⟨1215102469048743691872695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3240273250796649844993853 1215102469048743691872695)
          ·
            refine ⟨1822653703573115537809043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1215102469048743691872695 1822653703573115537809043)
            ·
              refine ⟨2733980555359673306713565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1822653703573115537809043 2733980555359673306713565)
              ·
                refine ⟨1025242708259877490017587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2733980555359673306713565 1025242708259877490017587)
                ·
                  refine ⟨1537864062389816235026381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1025242708259877490017587 1537864062389816235026381)
                  ·
                    refine ⟨576699023396181088134893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1537864062389816235026381 576699023396181088134893)
                    ·
                      refine ⟨216262133773567908050585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 576699023396181088134893 216262133773567908050585)
                      ·
                        rfl

theorem cell23_421169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_421169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421169 prefixEnd_421169 := by exact prefixLift 421169
  have htrace : WordTrace (prefixWord ++ tailWord_421169) baseStart_421169 baseEnd_421169 := by
    simpa [prefixWord, tailWord_421169, baseEnd_421169] using wordTrace_append hprefix tailTrace_421169
  have hstable : (prefixWord ++ tailWord_421169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421169).length < 2 ^ (prefixWord ++ tailWord_421169).sum := by decide
  have hdescent : baseEnd_421169 < baseStart_421169 := by decide
  rcases family_descends (prefixWord ++ tailWord_421169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421197 : List Nat := [1, 6, 1, 3, 2, 1, 1, 2, 2, 4]
def baseStart_421197 : Nat := 118140960795 + 421197 * 2 ^ 59
def prefixEnd_421197 : Nat := 4983230072969 + 3 ^ 40 * 421197 * 2
def baseEnd_421197 : Nat := 72092170410631266166819

theorem tailTrace_421197 : CollatzResearch.WordTrace tailWord_421197 prefixEnd_421197 72092170410631266166819 := by
  unfold tailWord_421197
  simp only [CollatzResearch.WordTrace]
  refine ⟨15362316655082678565693845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10241544436721785710462563 15362316655082678565693845)
  ·
    refine ⟨720108593207000557766899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15362316655082678565693845 720108593207000557766899)
    ·
      refine ⟨1080162889810500836650349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 720108593207000557766899 1080162889810500836650349)
      ·
        refine ⟨405061083678937813743881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1080162889810500836650349 405061083678937813743881)
        ·
          refine ⟨303795812759203360307911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 405061083678937813743881 303795812759203360307911)
          ·
            refine ⟨455693719138805040461867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303795812759203360307911 455693719138805040461867)
            ·
              refine ⟨683540578708207560692801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 455693719138805040461867 683540578708207560692801)
              ·
                refine ⟨512655434031155670519601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 683540578708207560692801 512655434031155670519601)
                ·
                  refine ⟨384491575523366752889701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 512655434031155670519601 384491575523366752889701)
                  ·
                    refine ⟨72092170410631266166819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 384491575523366752889701 72092170410631266166819)
                    ·
                      rfl

theorem cell23_421197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_421197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421197 prefixEnd_421197 := by exact prefixLift 421197
  have htrace : WordTrace (prefixWord ++ tailWord_421197) baseStart_421197 baseEnd_421197 := by
    simpa [prefixWord, tailWord_421197, baseEnd_421197] using wordTrace_append hprefix tailTrace_421197
  have hstable : (prefixWord ++ tailWord_421197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421197).length < 2 ^ (prefixWord ++ tailWord_421197).sum := by decide
  have hdescent : baseEnd_421197 < baseStart_421197 := by decide
  rcases family_descends (prefixWord ++ tailWord_421197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421209 : List Nat := [1, 2, 1, 2, 2, 2, 2, 2, 3, 4, 2]
def baseStart_421209 : Nat := 118140960795 + 421209 * 2 ^ 59
def prefixEnd_421209 : Nat := 4983230072969 + 3 ^ 40 * 421209 * 2
def baseEnd_421209 : Nat := 216282672999747751550401

theorem tailTrace_421209 : CollatzResearch.WordTrace tailWord_421209 prefixEnd_421209 216282672999747751550401 := by
  unfold tailWord_421209
  simp only [CollatzResearch.WordTrace]
  refine ⟨15362754331039204615130681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10241836220692803076753787 15362754331039204615130681)
  ·
    refine ⟨11522065748279403461348011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15362754331039204615130681 11522065748279403461348011)
    ·
      refine ⟨17283098622419105192022017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11522065748279403461348011 17283098622419105192022017)
      ·
        refine ⟨12962323966814328894016513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17283098622419105192022017 12962323966814328894016513)
        ·
          refine ⟨9721742975110746670512385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12962323966814328894016513 9721742975110746670512385)
          ·
            refine ⟨7291307231333060002884289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9721742975110746670512385 7291307231333060002884289)
            ·
              refine ⟨5468480423499795002163217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7291307231333060002884289 5468480423499795002163217)
              ·
                refine ⟨4101360317624846251622413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5468480423499795002163217 4101360317624846251622413)
                ·
                  refine ⟨1538010119109317344358405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4101360317624846251622413 1538010119109317344358405)
                  ·
                    refine ⟨288376897332997002067201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1538010119109317344358405 288376897332997002067201)
                    ·
                      refine ⟨216282672999747751550401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 288376897332997002067201 216282672999747751550401)
                      ·
                        rfl

theorem cell23_421209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 4, 2].length) (baseStart_421209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421209 prefixEnd_421209 := by exact prefixLift 421209
  have htrace : WordTrace (prefixWord ++ tailWord_421209) baseStart_421209 baseEnd_421209 := by
    simpa [prefixWord, tailWord_421209, baseEnd_421209] using wordTrace_append hprefix tailTrace_421209
  have hstable : (prefixWord ++ tailWord_421209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421209).length < 2 ^ (prefixWord ++ tailWord_421209).sum := by decide
  have hdescent : baseEnd_421209 < baseStart_421209 := by decide
  rcases family_descends (prefixWord ++ tailWord_421209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421232 : List Nat := [2, 1, 1, 1, 4, 2, 1, 4, 7]
def baseStart_421232 : Nat := 118140960795 + 421232 * 2 ^ 59
def prefixEnd_421232 : Nat := 4983230072969 + 3 ^ 40 * 421232 * 2
def baseEnd_421232 : Nat := 24032720339422351284755

theorem tailTrace_421232 : CollatzResearch.WordTrace tailWord_421232 prefixEnd_421232 24032720339422351284755 := by
  unfold tailWord_421232
  simp only [CollatzResearch.WordTrace]
  refine ⟨7681796604977939771608975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10242395473303919695478633 7681796604977939771608975)
  ·
    refine ⟨11522694907466909657413463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7681796604977939771608975 11522694907466909657413463)
    ·
      refine ⟨17284042361200364486120195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11522694907466909657413463 17284042361200364486120195)
      ·
        refine ⟨25926063541800546729180293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17284042361200364486120195 25926063541800546729180293)
        ·
          refine ⟨4861136914087602511721305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25926063541800546729180293 4861136914087602511721305)
          ·
            refine ⟨3645852685565701883790979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4861136914087602511721305 3645852685565701883790979)
            ·
              refine ⟨5468779028348552825686469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3645852685565701883790979 5468779028348552825686469)
              ·
                refine ⟨1025396067815353654816213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5468779028348552825686469 1025396067815353654816213)
                ·
                  refine ⟨24032720339422351284755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1025396067815353654816213 24032720339422351284755)
                  ·
                    rfl

theorem cell23_421232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 7].length) (baseStart_421232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421232 prefixEnd_421232 := by exact prefixLift 421232
  have htrace : WordTrace (prefixWord ++ tailWord_421232) baseStart_421232 baseEnd_421232 := by
    simpa [prefixWord, tailWord_421232, baseEnd_421232] using wordTrace_append hprefix tailTrace_421232
  have hstable : (prefixWord ++ tailWord_421232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421232).length < 2 ^ (prefixWord ++ tailWord_421232).sum := by decide
  have hdescent : baseEnd_421232 < baseStart_421232 := by decide
  rcases family_descends (prefixWord ++ tailWord_421232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421277 : List Nat := [1, 4, 2, 1, 3, 3, 2, 1, 2, 2, 2]
def baseStart_421277 : Nat := 118140960795 + 421277 * 2 ^ 59
def prefixEnd_421277 : Nat := 4983230072969 + 3 ^ 40 * 421277 * 2
def baseEnd_421277 : Nat := 216317589684253485500089

theorem tailTrace_421277 : CollatzResearch.WordTrace tailWord_421277 prefixEnd_421277 216317589684253485500089 := by
  unfold tailWord_421277
  simp only [CollatzResearch.WordTrace]
  refine ⟨15365234494792852228606085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10243489663195234819070723 15365234494792852228606085)
  ·
    refine ⟨2880981467773659792863641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15365234494792852228606085 2880981467773659792863641)
    ·
      refine ⟨2160736100830244844647731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2880981467773659792863641 2160736100830244844647731)
      ·
        refine ⟨3241104151245367266971597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2160736100830244844647731 3241104151245367266971597)
        ·
          refine ⟨1215414056717012725114349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3241104151245367266971597 1215414056717012725114349)
          ·
            refine ⟨455780271268879771917881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1215414056717012725114349 455780271268879771917881)
            ·
              refine ⟨341835203451659828938411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 455780271268879771917881 341835203451659828938411)
              ·
                refine ⟨512752805177489743407617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 341835203451659828938411 512752805177489743407617)
                ·
                  refine ⟨384564603883117307555713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 512752805177489743407617 384564603883117307555713)
                  ·
                    refine ⟨288423452912337980666785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 384564603883117307555713 288423452912337980666785)
                    ·
                      refine ⟨216317589684253485500089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 288423452912337980666785 216317589684253485500089)
                      ·
                        rfl

theorem cell23_421277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_421277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421277 prefixEnd_421277 := by exact prefixLift 421277
  have htrace : WordTrace (prefixWord ++ tailWord_421277) baseStart_421277 baseEnd_421277 := by
    simpa [prefixWord, tailWord_421277, baseEnd_421277] using wordTrace_append hprefix tailTrace_421277
  have hstable : (prefixWord ++ tailWord_421277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421277).length < 2 ^ (prefixWord ++ tailWord_421277).sum := by decide
  have hdescent : baseEnd_421277 < baseStart_421277 := by decide
  rcases family_descends (prefixWord ++ tailWord_421277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421292 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 2, 8]
def baseStart_421292 : Nat := 118140960795 + 421292 * 2 ^ 59
def prefixEnd_421292 : Nat := 4983230072969 + 3 ^ 40 * 421292 * 2
def baseEnd_421292 : Nat := 72108430631356975604173

theorem tailTrace_421292 : CollatzResearch.WordTrace tailWord_421292 prefixEnd_421292 72108430631356975604173 := by
  unfold tailWord_421292
  simp only [CollatzResearch.WordTrace]
  refine ⟨7682890794869254895201065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10243854393159006526934753 7682890794869254895201065)
  ·
    refine ⟨5762168096151941171400799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7682890794869254895201065 5762168096151941171400799)
    ·
      refine ⟨8643252144227911757101199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5762168096151941171400799 8643252144227911757101199)
      ·
        refine ⟨12964878216341867635651799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8643252144227911757101199 12964878216341867635651799)
        ·
          refine ⟨19447317324512801453477699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12964878216341867635651799 19447317324512801453477699)
          ·
            refine ⟨29170975986769202180216549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19447317324512801453477699 29170975986769202180216549)
            ·
              refine ⟨5469557997519225408790603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29170975986769202180216549 5469557997519225408790603)
              ·
                refine ⟨8204336996278838113185905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5469557997519225408790603 8204336996278838113185905)
                ·
                  refine ⟨6153252747209128584889429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8204336996278838113185905 6153252747209128584889429)
                  ·
                    refine ⟨72108430631356975604173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 6153252747209128584889429 72108430631356975604173)
                    ·
                      rfl

theorem cell23_421292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 8].length) (baseStart_421292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421292 prefixEnd_421292 := by exact prefixLift 421292
  have htrace : WordTrace (prefixWord ++ tailWord_421292) baseStart_421292 baseEnd_421292 := by
    simpa [prefixWord, tailWord_421292, baseEnd_421292] using wordTrace_append hprefix tailTrace_421292
  have hstable : (prefixWord ++ tailWord_421292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421292).length < 2 ^ (prefixWord ++ tailWord_421292).sum := by decide
  have hdescent : baseEnd_421292 < baseStart_421292 := by decide
  rcases family_descends (prefixWord ++ tailWord_421292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421383 : List Nat := [1, 1, 4, 3, 2, 1, 1, 3, 3, 1, 3]
def baseStart_421383 : Nat := 118140960795 + 421383 * 2 ^ 59
def prefixEnd_421383 : Nat := 4983230072969 + 3 ^ 40 * 421383 * 2
def baseEnd_421383 : Nat := 216372018633630070774601

theorem tailTrace_421383 : CollatzResearch.WordTrace tailWord_421383 prefixEnd_421383 216372018633630070774601 := by
  unfold tailWord_421383
  simp only [CollatzResearch.WordTrace]
  refine ⟨15369100632408832331964803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10246067088272554887976535 15369100632408832331964803)
  ·
    refine ⟨23053650948613248497947205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15369100632408832331964803 23053650948613248497947205)
    ·
      refine ⟨4322559552864984093365101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23053650948613248497947205 4322559552864984093365101)
      ·
        refine ⟨1620959832324369035011913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4322559552864984093365101 1620959832324369035011913)
        ·
          refine ⟨1215719874243276776258935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1620959832324369035011913 1215719874243276776258935)
          ·
            refine ⟨1823579811364915164388403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1215719874243276776258935 1823579811364915164388403)
            ·
              refine ⟨2735369717047372746582605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1823579811364915164388403 2735369717047372746582605)
              ·
                refine ⟨1025763643892764779968477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2735369717047372746582605 1025763643892764779968477)
                ·
                  refine ⟨384661366459786792488179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1025763643892764779968477 384661366459786792488179)
                  ·
                    refine ⟨576992049689680188732269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 384661366459786792488179 576992049689680188732269)
                    ·
                      refine ⟨216372018633630070774601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 576992049689680188732269 216372018633630070774601)
                      ·
                        rfl

theorem cell23_421383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_421383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421383 prefixEnd_421383 := by exact prefixLift 421383
  have htrace : WordTrace (prefixWord ++ tailWord_421383) baseStart_421383 baseEnd_421383 := by
    simpa [prefixWord, tailWord_421383, baseEnd_421383] using wordTrace_append hprefix tailTrace_421383
  have hstable : (prefixWord ++ tailWord_421383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421383).length < 2 ^ (prefixWord ++ tailWord_421383).sum := by decide
  have hdescent : baseEnd_421383 < baseStart_421383 := by decide
  rcases family_descends (prefixWord ++ tailWord_421383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421426 : List Nat := [3, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3]
def baseStart_421426 : Nat := 118140960795 + 421426 * 2 ^ 59
def prefixEnd_421426 : Nat := 4983230072969 + 3 ^ 40 * 421426 * 2
def baseEnd_421426 : Nat := 216394098301773402536903

theorem tailTrace_421426 : CollatzResearch.WordTrace tailWord_421426 prefixEnd_421426 216394098301773402536903 := by
  unfold tailWord_421426
  simp only [CollatzResearch.WordTrace]
  refine ⟨3842667242813262668945033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10247112647502033783853421 3842667242813262668945033)
  ·
    refine ⟨2882000432109947001708775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3842667242813262668945033 2882000432109947001708775)
    ·
      refine ⟨4323000648164920502563163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2882000432109947001708775 4323000648164920502563163)
      ·
        refine ⟨6484500972247380753844745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4323000648164920502563163 6484500972247380753844745)
        ·
          refine ⟨4863375729185535565383559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6484500972247380753844745 4863375729185535565383559)
          ·
            refine ⟨7295063593778303348075339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4863375729185535565383559 7295063593778303348075339)
            ·
              refine ⟨10942595390667455022113009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7295063593778303348075339 10942595390667455022113009)
              ·
                refine ⟨8206946543000591266584757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10942595390667455022113009 8206946543000591266584757)
                ·
                  refine ⟨769401238406305431242321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8206946543000591266584757 769401238406305431242321)
                  ·
                    refine ⟨577050928804729073431741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 769401238406305431242321 577050928804729073431741)
                    ·
                      refine ⟨216394098301773402536903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 577050928804729073431741 216394098301773402536903)
                      ·
                        rfl

theorem cell23_421426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_421426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421426 prefixEnd_421426 := by exact prefixLift 421426
  have htrace : WordTrace (prefixWord ++ tailWord_421426) baseStart_421426 baseEnd_421426 := by
    simpa [prefixWord, tailWord_421426, baseEnd_421426] using wordTrace_append hprefix tailTrace_421426
  have hstable : (prefixWord ++ tailWord_421426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421426).length < 2 ^ (prefixWord ++ tailWord_421426).sum := by decide
  have hdescent : baseEnd_421426 < baseStart_421426 := by decide
  rcases family_descends (prefixWord ++ tailWord_421426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421429 : List Nat := [1, 3, 3, 1, 1, 3, 11]
def baseStart_421429 : Nat := 118140960795 + 421429 * 2 ^ 59
def prefixEnd_421429 : Nat := 4983230072969 + 3 ^ 40 * 421429 * 2
def baseEnd_421429 : Nat := 2671551095601690009869

theorem tailTrace_421429 : CollatzResearch.WordTrace tailWord_421429 prefixEnd_421429 2671551095601690009869 := by
  unfold tailWord_421429
  simp only [CollatzResearch.WordTrace]
  refine ⟨15370778390242182188139341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10247185593494788125426227 15370778390242182188139341)
  ·
    refine ⟨5764041896340818320552253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15370778390242182188139341 5764041896340818320552253)
    ·
      refine ⟨2161515711127806870207095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5764041896340818320552253 2161515711127806870207095)
      ·
        refine ⟨3242273566691710305310643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2161515711127806870207095 3242273566691710305310643)
        ·
          refine ⟨4863410350037565457965965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3242273566691710305310643 4863410350037565457965965)
          ·
            refine ⟨1823778881264087046737237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4863410350037565457965965 1823778881264087046737237)
            ·
              refine ⟨2671551095601690009869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 1823778881264087046737237 2671551095601690009869)
              ·
                rfl

theorem cell23_421429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 11].length) (baseStart_421429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421429 prefixEnd_421429 := by exact prefixLift 421429
  have htrace : WordTrace (prefixWord ++ tailWord_421429) baseStart_421429 baseEnd_421429 := by
    simpa [prefixWord, tailWord_421429, baseEnd_421429] using wordTrace_append hprefix tailTrace_421429
  have hstable : (prefixWord ++ tailWord_421429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421429).length < 2 ^ (prefixWord ++ tailWord_421429).sum := by decide
  have hdescent : baseEnd_421429 < baseStart_421429 := by decide
  rcases family_descends (prefixWord ++ tailWord_421429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421456 : List Nat := [2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 3]
def baseStart_421456 : Nat := 118140960795 + 421456 * 2 ^ 59
def prefixEnd_421456 : Nat := 4983230072969 + 3 ^ 40 * 421456 * 2
def baseEnd_421456 : Nat := 216409502721408285161765

theorem tailTrace_421456 : CollatzResearch.WordTrace tailWord_421456 prefixEnd_421456 216409502721408285161765 := by
  unfold tailWord_421456
  simp only [CollatzResearch.WordTrace]
  refine ⟨7685881580572182899686111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10247842107429577199581481 7685881580572182899686111)
  ·
    refine ⟨11528822370858274349529167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7685881580572182899686111 11528822370858274349529167)
    ·
      refine ⟨17293233556287411524293751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11528822370858274349529167 17293233556287411524293751)
      ·
        refine ⟨25939850334431117286440627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17293233556287411524293751 25939850334431117286440627)
        ·
          refine ⟨38909775501646675929660941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25939850334431117286440627 38909775501646675929660941)
          ·
            refine ⟨14591165813117503473622853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38909775501646675929660941 14591165813117503473622853)
            ·
              refine ⟨2735843589959531901304285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14591165813117503473622853 2735843589959531901304285)
              ·
                refine ⟨1025941346234824462989107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2735843589959531901304285 1025941346234824462989107)
                ·
                  refine ⟨1538912019352236694483661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1025941346234824462989107 1538912019352236694483661)
                  ·
                    refine ⟨577092007257088760431373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1538912019352236694483661 577092007257088760431373)
                    ·
                      refine ⟨216409502721408285161765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 577092007257088760431373 216409502721408285161765)
                      ·
                        rfl

theorem cell23_421456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 3].length) (baseStart_421456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421456 prefixEnd_421456 := by exact prefixLift 421456
  have htrace : WordTrace (prefixWord ++ tailWord_421456) baseStart_421456 baseEnd_421456 := by
    simpa [prefixWord, tailWord_421456, baseEnd_421456] using wordTrace_append hprefix tailTrace_421456
  have hstable : (prefixWord ++ tailWord_421456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421456).length < 2 ^ (prefixWord ++ tailWord_421456).sum := by decide
  have hdescent : baseEnd_421456 < baseStart_421456 := by decide
  rcases family_descends (prefixWord ++ tailWord_421456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421489 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 3, 8]
def baseStart_421489 : Nat := 118140960795 + 421489 * 2 ^ 59
def prefixEnd_421489 : Nat := 4983230072969 + 3 ^ 40 * 421489 * 2
def baseEnd_421489 : Nat := 72142149194335552016371

theorem tailTrace_421489 : CollatzResearch.WordTrace tailWord_421489 prefixEnd_421489 72142149194335552016371 := by
  unfold tailWord_421489
  simp only [CollatzResearch.WordTrace]
  refine ⟨15372966770024812435323521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10248644513349874956882347 15372966770024812435323521)
  ·
    refine ⟨11529725077518609326492641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15372966770024812435323521 11529725077518609326492641)
    ·
      refine ⟨8647293808138956994869481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11529725077518609326492641 8647293808138956994869481)
      ·
        refine ⟨6485470356104217746152111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8647293808138956994869481 6485470356104217746152111)
        ·
          refine ⟨9728205534156326619228167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6485470356104217746152111 9728205534156326619228167)
          ·
            refine ⟨14592308301234489928842251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9728205534156326619228167 14592308301234489928842251)
            ·
              refine ⟨21888462451851734893263377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14592308301234489928842251 21888462451851734893263377)
              ·
                refine ⟨16416346838888801169947533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21888462451851734893263377 16416346838888801169947533)
                ·
                  refine ⟨6156130064583300438730325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16416346838888801169947533 6156130064583300438730325)
                  ·
                    refine ⟨72142149194335552016371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 6156130064583300438730325 72142149194335552016371)
                    ·
                      rfl

theorem cell23_421489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 8].length) (baseStart_421489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421489 prefixEnd_421489 := by exact prefixLift 421489
  have htrace : WordTrace (prefixWord ++ tailWord_421489) baseStart_421489 baseEnd_421489 := by
    simpa [prefixWord, tailWord_421489, baseEnd_421489] using wordTrace_append hprefix tailTrace_421489
  have hstable : (prefixWord ++ tailWord_421489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421489).length < 2 ^ (prefixWord ++ tailWord_421489).sum := by decide
  have hdescent : baseEnd_421489 < baseStart_421489 := by decide
  rcases family_descends (prefixWord ++ tailWord_421489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421490 : List Nat := [3, 2, 1, 2, 3, 1, 1, 4, 2, 1, 3]
def baseStart_421490 : Nat := 118140960795 + 421490 * 2 ^ 59
def prefixEnd_421490 : Nat := 4983230072969 + 3 ^ 40 * 421490 * 2
def baseEnd_421490 : Nat := 216426961063661152136609

theorem tailTrace_421490 : CollatzResearch.WordTrace tailWord_421490 prefixEnd_421490 216426961063661152136609 := by
  unfold tailWord_421490
  simp only [CollatzResearch.WordTrace]
  refine ⟨3843250810755297401527481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10248668828680793070739949 3843250810755297401527481)
  ·
    refine ⟨2882438108066473051145611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3843250810755297401527481 2882438108066473051145611)
    ·
      refine ⟨4323657162099709576718417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2882438108066473051145611 4323657162099709576718417)
      ·
        refine ⟨3242742871574782182538813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4323657162099709576718417 3242742871574782182538813)
        ·
          refine ⟨1216028576840543318452055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3242742871574782182538813 1216028576840543318452055)
          ·
            refine ⟨1824042865260814977678083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1216028576840543318452055 1824042865260814977678083)
            ·
              refine ⟨2736064297891222466517125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1824042865260814977678083 2736064297891222466517125)
              ·
                refine ⟨513012055854604212471961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2736064297891222466517125 513012055854604212471961)
                ·
                  refine ⟨384759041890953159353971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 513012055854604212471961 384759041890953159353971)
                  ·
                    refine ⟨577138562836429739030957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 384759041890953159353971 577138562836429739030957)
                    ·
                      refine ⟨216426961063661152136609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 577138562836429739030957 216426961063661152136609)
                      ·
                        rfl

theorem cell23_421490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_421490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421490 prefixEnd_421490 := by exact prefixLift 421490
  have htrace : WordTrace (prefixWord ++ tailWord_421490) baseStart_421490 baseEnd_421490 := by
    simpa [prefixWord, tailWord_421490, baseEnd_421490] using wordTrace_append hprefix tailTrace_421490
  have hstable : (prefixWord ++ tailWord_421490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421490).length < 2 ^ (prefixWord ++ tailWord_421490).sum := by decide
  have hdescent : baseEnd_421490 < baseStart_421490 := by decide
  rcases family_descends (prefixWord ++ tailWord_421490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421513 : List Nat := [1, 2, 1, 1, 4, 1, 3, 3, 1, 4, 2]
def baseStart_421513 : Nat := 118140960795 + 421513 * 2 ^ 59
def prefixEnd_421513 : Nat := 4983230072969 + 3 ^ 40 * 421513 * 2
def baseEnd_421513 : Nat := 216438771118714562149003

theorem tailTrace_421513 : CollatzResearch.WordTrace tailWord_421513 prefixEnd_421513 216438771118714562149003 := by
  unfold tailWord_421513
  simp only [CollatzResearch.WordTrace]
  refine ⟨15373842121937864534197193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10249228081291909689464795 15373842121937864534197193)
  ·
    refine ⟨11530381591453398400647895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15373842121937864534197193 11530381591453398400647895)
    ·
      refine ⟨17295572387180097600971843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11530381591453398400647895 17295572387180097600971843)
      ·
        refine ⟨25943358580770146401457765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17295572387180097600971843 25943358580770146401457765)
        ·
          refine ⟨4864379733894402450273331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25943358580770146401457765 4864379733894402450273331)
          ·
            refine ⟨7296569600841603675409997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4864379733894402450273331 7296569600841603675409997)
            ·
              refine ⟨2736213600315601378278749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7296569600841603675409997 2736213600315601378278749)
              ·
                refine ⟨1026080100118350516854531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2736213600315601378278749 1026080100118350516854531)
                ·
                  refine ⟨1539120150177525775281797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1026080100118350516854531 1539120150177525775281797)
                  ·
                    refine ⟨288585028158286082865337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1539120150177525775281797 288585028158286082865337)
                    ·
                      refine ⟨216438771118714562149003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 288585028158286082865337 216438771118714562149003)
                      ·
                        rfl

theorem cell23_421513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 4, 2].length) (baseStart_421513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421513 prefixEnd_421513 := by exact prefixLift 421513
  have htrace : WordTrace (prefixWord ++ tailWord_421513) baseStart_421513 baseEnd_421513 := by
    simpa [prefixWord, tailWord_421513, baseEnd_421513] using wordTrace_append hprefix tailTrace_421513
  have hstable : (prefixWord ++ tailWord_421513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421513).length < 2 ^ (prefixWord ++ tailWord_421513).sum := by decide
  have hdescent : baseEnd_421513 < baseStart_421513 := by decide
  rcases family_descends (prefixWord ++ tailWord_421513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421516 : List Nat := [2, 2, 1, 2, 1, 1, 3, 2, 2, 4, 3]
def baseStart_421516 : Nat := 118140960795 + 421516 * 2 ^ 59
def prefixEnd_421516 : Nat := 4983230072969 + 3 ^ 40 * 421516 * 2
def baseEnd_421516 : Nat := 216440311560678050411489

theorem tailTrace_421516 : CollatzResearch.WordTrace tailWord_421516 prefixEnd_421516 216440311560678050411489 := by
  unfold tailWord_421516
  simp only [CollatzResearch.WordTrace]
  refine ⟨7686975770463498023278201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10249301027284664031037601 7686975770463498023278201)
  ·
    refine ⟨5765231827847623517458651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7686975770463498023278201 5765231827847623517458651)
    ·
      refine ⟨8647847741771435276187977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5765231827847623517458651 8647847741771435276187977)
      ·
        refine ⟨6485885806328576457140983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8647847741771435276187977 6485885806328576457140983)
        ·
          refine ⟨9728828709492864685711475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6485885806328576457140983 9728828709492864685711475)
          ·
            refine ⟨14593243064239297028567213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9728828709492864685711475 14593243064239297028567213)
            ·
              refine ⟨5472466149089736385712705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14593243064239297028567213 5472466149089736385712705)
              ·
                refine ⟨4104349611817302289284529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5472466149089736385712705 4104349611817302289284529)
                ·
                  refine ⟨3078262208862976716963397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4104349611817302289284529 3078262208862976716963397)
                  ·
                    refine ⟨577174164161808134430637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3078262208862976716963397 577174164161808134430637)
                    ·
                      refine ⟨216440311560678050411489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 577174164161808134430637 216440311560678050411489)
                      ·
                        rfl

theorem cell23_421516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2, 4, 3].length) (baseStart_421516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421516 prefixEnd_421516 := by exact prefixLift 421516
  have htrace : WordTrace (prefixWord ++ tailWord_421516) baseStart_421516 baseEnd_421516 := by
    simpa [prefixWord, tailWord_421516, baseEnd_421516] using wordTrace_append hprefix tailTrace_421516
  have hstable : (prefixWord ++ tailWord_421516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421516).length < 2 ^ (prefixWord ++ tailWord_421516).sum := by decide
  have hdescent : baseEnd_421516 < baseStart_421516 := by decide
  rcases family_descends (prefixWord ++ tailWord_421516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421534 : List Nat := [4, 3, 1, 1, 1, 2, 4, 1, 1, 3, 2]
def baseStart_421534 : Nat := 118140960795 + 421534 * 2 ^ 59
def prefixEnd_421534 : Nat := 4983230072969 + 3 ^ 40 * 421534 * 2
def baseEnd_421534 : Nat := 216449554212458979986407

theorem tailTrace_421534 : CollatzResearch.WordTrace tailWord_421534 prefixEnd_421534 216449554212458979986407 := by
  unfold tailWord_421534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1921826006857723140088957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10249738703241190080474437 1921826006857723140088957)
  ·
    refine ⟨720684752571646177533359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1921826006857723140088957 720684752571646177533359)
    ·
      refine ⟨1081027128857469266300039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 720684752571646177533359 1081027128857469266300039)
      ·
        refine ⟨1621540693286203899450059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1081027128857469266300039 1621540693286203899450059)
        ·
          refine ⟨2432311039929305849175089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1621540693286203899450059 2432311039929305849175089)
          ·
            refine ⟨1824233279946979386881317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2432311039929305849175089 1824233279946979386881317)
            ·
              refine ⟨342043739990058635040247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1824233279946979386881317 342043739990058635040247)
              ·
                refine ⟨513065609985087952560371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 342043739990058635040247 513065609985087952560371)
                ·
                  refine ⟨769598414977631928840557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 513065609985087952560371 769598414977631928840557)
                  ·
                    refine ⟨288599405616611973315209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 769598414977631928840557 288599405616611973315209)
                    ·
                      refine ⟨216449554212458979986407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 288599405616611973315209 216449554212458979986407)
                      ·
                        rfl

theorem cell23_421534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_421534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421534 prefixEnd_421534 := by exact prefixLift 421534
  have htrace : WordTrace (prefixWord ++ tailWord_421534) baseStart_421534 baseEnd_421534 := by
    simpa [prefixWord, tailWord_421534, baseEnd_421534] using wordTrace_append hprefix tailTrace_421534
  have hstable : (prefixWord ++ tailWord_421534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421534).length < 2 ^ (prefixWord ++ tailWord_421534).sum := by decide
  have hdescent : baseEnd_421534 < baseStart_421534 := by decide
  rcases family_descends (prefixWord ++ tailWord_421534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421564 : List Nat := [2, 2, 2, 3, 1, 3, 3, 1, 2, 2, 2]
def baseStart_421564 : Nat := 118140960795 + 421564 * 2 ^ 59
def prefixEnd_421564 : Nat := 4983230072969 + 3 ^ 40 * 421564 * 2
def baseEnd_421564 : Nat := 216464958632093862611269

theorem tailTrace_421564 : CollatzResearch.WordTrace tailWord_421564 prefixEnd_421564 216464958632093862611269 := by
  unfold tailWord_421564
  simp only [CollatzResearch.WordTrace]
  refine ⟨7687851122376550122151873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10250468163168733496202497 7687851122376550122151873)
  ·
    refine ⟨5765888341782412591613905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7687851122376550122151873 5765888341782412591613905)
    ·
      refine ⟨4324416256336809443710429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5765888341782412591613905 4324416256336809443710429)
      ·
        refine ⟨1621656096126303541391411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4324416256336809443710429 1621656096126303541391411)
        ·
          refine ⟨2432484144189455312087117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1621656096126303541391411 2432484144189455312087117)
          ·
            refine ⟨912181554071045742032669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2432484144189455312087117 912181554071045742032669)
            ·
              refine ⟨342068082776642153262251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 912181554071045742032669 342068082776642153262251)
              ·
                refine ⟨513102124164963229893377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 342068082776642153262251 513102124164963229893377)
                ·
                  refine ⟨384826593123722422420033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 513102124164963229893377 384826593123722422420033)
                  ·
                    refine ⟨288619944842791816815025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 384826593123722422420033 288619944842791816815025)
                    ·
                      refine ⟨216464958632093862611269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 288619944842791816815025 216464958632093862611269)
                      ·
                        rfl

theorem cell23_421564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_421564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421564 prefixEnd_421564 := by exact prefixLift 421564
  have htrace : WordTrace (prefixWord ++ tailWord_421564) baseStart_421564 baseEnd_421564 := by
    simpa [prefixWord, tailWord_421564, baseEnd_421564] using wordTrace_append hprefix tailTrace_421564
  have hstable : (prefixWord ++ tailWord_421564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421564).length < 2 ^ (prefixWord ++ tailWord_421564).sum := by decide
  have hdescent : baseEnd_421564 < baseStart_421564 := by decide
  rcases family_descends (prefixWord ++ tailWord_421564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421616 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 4]
def baseStart_421616 : Nat := 118140960795 + 421616 * 2 ^ 59
def prefixEnd_421616 : Nat := 4983230072969 + 3 ^ 40 * 421616 * 2
def baseEnd_421616 : Nat := 216491659626127659161029

theorem tailTrace_421616 : CollatzResearch.WordTrace tailWord_421616 prefixEnd_421616 216491659626127659161029 := by
  unfold tailWord_421616
  simp only [CollatzResearch.WordTrace]
  refine ⟨7688799420282356562598351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10251732560376475416797801 7688799420282356562598351)
  ·
    refine ⟨11533199130423534843897527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7688799420282356562598351 11533199130423534843897527)
    ·
      refine ⟨17299798695635302265846291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11533199130423534843897527 17299798695635302265846291)
      ·
        refine ⟨25949698043452953398769437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17299798695635302265846291 25949698043452953398769437)
        ·
          refine ⟨9731136766294857524538539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25949698043452953398769437 9731136766294857524538539)
          ·
            refine ⟨14596705149442286286807809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9731136766294857524538539 14596705149442286286807809)
            ·
              refine ⟨10947528862081714715105857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14596705149442286286807809 10947528862081714715105857)
              ·
                refine ⟨8210646646561286036329393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10947528862081714715105857 8210646646561286036329393)
                ·
                  refine ⟨6157984984920964527247045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8210646646561286036329393 6157984984920964527247045)
                  ·
                    refine ⟨1154622184672680848858821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6157984984920964527247045 1154622184672680848858821)
                    ·
                      refine ⟨216491659626127659161029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1154622184672680848858821 216491659626127659161029)
                      ·
                        rfl

theorem cell23_421616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 4].length) (baseStart_421616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421616 prefixEnd_421616 := by exact prefixLift 421616
  have htrace : WordTrace (prefixWord ++ tailWord_421616) baseStart_421616 baseEnd_421616 := by
    simpa [prefixWord, tailWord_421616, baseEnd_421616] using wordTrace_append hprefix tailTrace_421616
  have hstable : (prefixWord ++ tailWord_421616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421616).length < 2 ^ (prefixWord ++ tailWord_421616).sum := by decide
  have hdescent : baseEnd_421616 < baseStart_421616 := by decide
  rcases family_descends (prefixWord ++ tailWord_421616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421640 : List Nat := [2, 1, 3, 2, 2, 1, 4, 1, 2, 2, 3]
def baseStart_421640 : Nat := 118140960795 + 421640 * 2 ^ 59
def prefixEnd_421640 : Nat := 4983230072969 + 3 ^ 40 * 421640 * 2
def baseEnd_421640 : Nat := 216503983161835565260919

theorem tailTrace_421640 : CollatzResearch.WordTrace tailWord_421640 prefixEnd_421640 216503983161835565260919 := by
  unfold tailWord_421640
  simp only [CollatzResearch.WordTrace]
  refine ⟨7689237096238882612035187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10252316128318510149380249 7689237096238882612035187)
  ·
    refine ⟨11533855644358323918052781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7689237096238882612035187 11533855644358323918052781)
    ·
      refine ⟨4325195866634371469269793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11533855644358323918052781 4325195866634371469269793)
      ·
        refine ⟨3243896899975778601952345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4325195866634371469269793 3243896899975778601952345)
        ·
          refine ⟨2432922674981833951464259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3243896899975778601952345 2432922674981833951464259)
          ·
            refine ⟨3649384012472750927196389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2432922674981833951464259 3649384012472750927196389)
            ·
              refine ⟨684259502338640798849323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3649384012472750927196389 684259502338640798849323)
              ·
                refine ⟨1026389253507961198273985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 684259502338640798849323 1026389253507961198273985)
                ·
                  refine ⟨769791940130970898705489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1026389253507961198273985 769791940130970898705489)
                  ·
                    refine ⟨577343955098228174029117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 769791940130970898705489 577343955098228174029117)
                    ·
                      refine ⟨216503983161835565260919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 577343955098228174029117 216503983161835565260919)
                      ·
                        rfl

theorem cell23_421640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_421640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421640 prefixEnd_421640 := by exact prefixLift 421640
  have htrace : WordTrace (prefixWord ++ tailWord_421640) baseStart_421640 baseEnd_421640 := by
    simpa [prefixWord, tailWord_421640, baseEnd_421640] using wordTrace_append hprefix tailTrace_421640
  have hstable : (prefixWord ++ tailWord_421640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421640).length < 2 ^ (prefixWord ++ tailWord_421640).sum := by decide
  have hdescent : baseEnd_421640 < baseStart_421640 := by decide
  rcases family_descends (prefixWord ++ tailWord_421640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421703 : List Nat := [1, 1, 4, 1, 2, 1, 4, 2, 1, 6]
def baseStart_421703 : Nat := 118140960795 + 421703 * 2 ^ 59
def prefixEnd_421703 : Nat := 4983230072969 + 3 ^ 40 * 421703 * 2
def baseEnd_421703 : Nat := 72178777481022939591043

theorem tailTrace_421703 : CollatzResearch.WordTrace tailWord_421703 prefixEnd_421703 72178777481022939591043 := by
  unfold tailWord_421703
  simp only [CollatzResearch.WordTrace]
  refine ⟨15380771991249526983613763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10253847994166351322409175 15380771991249526983613763)
  ·
    refine ⟨23071157986874290475420645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15380771991249526983613763 23071157986874290475420645)
    ·
      refine ⟨4325842122538929464141371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23071157986874290475420645 4325842122538929464141371)
      ·
        refine ⟨6488763183808394196212057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4325842122538929464141371 6488763183808394196212057)
        ·
          refine ⟨4866572387856295647159043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6488763183808394196212057 4866572387856295647159043)
          ·
            refine ⟨7299858581784443470738565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4866572387856295647159043 7299858581784443470738565)
            ·
              refine ⟨1368723484084583150763481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7299858581784443470738565 1368723484084583150763481)
              ·
                refine ⟨1026542613063437363072611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1368723484084583150763481 1026542613063437363072611)
                ·
                  refine ⟨1539813919595156044608917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1026542613063437363072611 1539813919595156044608917)
                  ·
                    refine ⟨72178777481022939591043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1539813919595156044608917 72178777481022939591043)
                    ·
                      rfl

theorem cell23_421703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_421703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421703 prefixEnd_421703 := by exact prefixLift 421703
  have htrace : WordTrace (prefixWord ++ tailWord_421703) baseStart_421703 baseEnd_421703 := by
    simpa [prefixWord, tailWord_421703, baseEnd_421703] using wordTrace_append hprefix tailTrace_421703
  have hstable : (prefixWord ++ tailWord_421703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421703).length < 2 ^ (prefixWord ++ tailWord_421703).sum := by decide
  have hdescent : baseEnd_421703 < baseStart_421703 := by decide
  rcases family_descends (prefixWord ++ tailWord_421703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421704 : List Nat := [2, 1, 3, 1, 1, 5, 2, 3, 1, 1, 3]
def baseStart_421704 : Nat := 118140960795 + 421704 * 2 ^ 59
def prefixEnd_421704 : Nat := 4983230072969 + 3 ^ 40 * 421704 * 2
def baseEnd_421704 : Nat := 216536845923723314860625

theorem tailTrace_421704 : CollatzResearch.WordTrace tailWord_421704 prefixEnd_421704 216536845923723314860625 := by
  unfold tailWord_421704
  simp only [CollatzResearch.WordTrace]
  refine ⟨7690404232122952077200083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10253872309497269436266777 7690404232122952077200083)
  ·
    refine ⟨11535606348184428115800125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7690404232122952077200083 11535606348184428115800125)
    ·
      refine ⟨4325852380569160543425047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11535606348184428115800125 4325852380569160543425047)
      ·
        refine ⟨6488778570853740815137571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4325852380569160543425047 6488778570853740815137571)
        ·
          refine ⟨9733167856280611222706357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6488778570853740815137571 9733167856280611222706357)
          ·
            refine ⟨912484486526307302128721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9733167856280611222706357 912484486526307302128721)
            ·
              refine ⟨684363364894730476596541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 912484486526307302128721 684363364894730476596541)
              ·
                refine ⟨256636261835523928723703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 684363364894730476596541 256636261835523928723703)
                ·
                  refine ⟨384954392753285893085555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 256636261835523928723703 384954392753285893085555)
                  ·
                    refine ⟨577431589129928839628333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 384954392753285893085555 577431589129928839628333)
                    ·
                      refine ⟨216536845923723314860625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 577431589129928839628333 216536845923723314860625)
                      ·
                        rfl

theorem cell23_421704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 3, 1, 1, 3].length) (baseStart_421704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421704 prefixEnd_421704 := by exact prefixLift 421704
  have htrace : WordTrace (prefixWord ++ tailWord_421704) baseStart_421704 baseEnd_421704 := by
    simpa [prefixWord, tailWord_421704, baseEnd_421704] using wordTrace_append hprefix tailTrace_421704
  have hstable : (prefixWord ++ tailWord_421704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421704).length < 2 ^ (prefixWord ++ tailWord_421704).sum := by decide
  have hdescent : baseEnd_421704 < baseStart_421704 := by decide
  rcases family_descends (prefixWord ++ tailWord_421704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421727 : List Nat := [1, 1, 2, 3, 1, 4, 1, 3, 3, 2, 2]
def baseStart_421727 : Nat := 118140960795 + 421727 * 2 ^ 59
def prefixEnd_421727 : Nat := 4983230072969 + 3 ^ 40 * 421727 * 2
def baseEnd_421727 : Nat := 216548655978776724873019

theorem tailTrace_421727 : CollatzResearch.WordTrace tailWord_421727 prefixEnd_421727 216548655978776724873019 := by
  unfold tailWord_421727
  simp only [CollatzResearch.WordTrace]
  refine ⟨15381647343162579082487435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10254431562108386054991623 15381647343162579082487435)
  ·
    refine ⟨23072471014743868623731153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15381647343162579082487435 23072471014743868623731153)
    ·
      refine ⟨17304353261057901467798365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23072471014743868623731153 17304353261057901467798365)
      ·
        refine ⟨6489132472896713050424387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17304353261057901467798365 6489132472896713050424387)
        ·
          refine ⟨9733698709345069575636581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6489132472896713050424387 9733698709345069575636581)
          ·
            refine ⟨1825068508002200545431859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9733698709345069575636581 1825068508002200545431859)
            ·
              refine ⟨2737602762003300818147789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1825068508002200545431859 2737602762003300818147789)
              ·
                refine ⟨1026601035751237806805421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2737602762003300818147789 1026601035751237806805421)
                ·
                  refine ⟨384975388406714177552033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1026601035751237806805421 384975388406714177552033)
                  ·
                    refine ⟨288731541305035633164025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 384975388406714177552033 288731541305035633164025)
                    ·
                      refine ⟨216548655978776724873019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 288731541305035633164025 216548655978776724873019)
                      ·
                        rfl

theorem cell23_421727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 3, 2, 2].length) (baseStart_421727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421727 prefixEnd_421727 := by exact prefixLift 421727
  have htrace : WordTrace (prefixWord ++ tailWord_421727) baseStart_421727 baseEnd_421727 := by
    simpa [prefixWord, tailWord_421727, baseEnd_421727] using wordTrace_append hprefix tailTrace_421727
  have hstable : (prefixWord ++ tailWord_421727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421727).length < 2 ^ (prefixWord ++ tailWord_421727).sum := by decide
  have hdescent : baseEnd_421727 < baseStart_421727 := by decide
  rcases family_descends (prefixWord ++ tailWord_421727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421730 : List Nat := [3, 3, 2, 1, 2, 1, 1, 1, 3, 1, 5]
def baseStart_421730 : Nat := 118140960795 + 421730 * 2 ^ 59
def prefixEnd_421730 : Nat := 4983230072969 + 3 ^ 40 * 421730 * 2
def baseEnd_421730 : Nat := 216550196420740213135505

theorem tailTrace_421730 : CollatzResearch.WordTrace tailWord_421730 prefixEnd_421730 216550196420740213135505 := by
  unfold tailWord_421730
  simp only [CollatzResearch.WordTrace]
  refine ⟨3845439190537927648711661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10254504508101140396564429 3845439190537927648711661)
  ·
    refine ⟨1442039696451722868266873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3845439190537927648711661 1442039696451722868266873)
    ·
      refine ⟨1081529772338792151200155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1442039696451722868266873 1081529772338792151200155)
      ·
        refine ⟨1622294658508188226800233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1081529772338792151200155 1622294658508188226800233)
        ·
          refine ⟨1216720993881141170100175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1622294658508188226800233 1216720993881141170100175)
          ·
            refine ⟨1825081490821711755150263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1216720993881141170100175 1825081490821711755150263)
            ·
              refine ⟨2737622236232567632725395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1825081490821711755150263 2737622236232567632725395)
              ·
                refine ⟨4106433354348851449088093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2737622236232567632725395 4106433354348851449088093)
                ·
                  refine ⟨1539912507880819293408035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4106433354348851449088093 1539912507880819293408035)
                  ·
                    refine ⟨2309868761821228940112053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1539912507880819293408035 2309868761821228940112053)
                    ·
                      refine ⟨216550196420740213135505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2309868761821228940112053 216550196420740213135505)
                      ·
                        rfl

theorem cell23_421730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_421730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421730 prefixEnd_421730 := by exact prefixLift 421730
  have htrace : WordTrace (prefixWord ++ tailWord_421730) baseStart_421730 baseEnd_421730 := by
    simpa [prefixWord, tailWord_421730, baseEnd_421730] using wordTrace_append hprefix tailTrace_421730
  have hstable : (prefixWord ++ tailWord_421730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421730).length < 2 ^ (prefixWord ++ tailWord_421730).sum := by decide
  have hdescent : baseEnd_421730 < baseStart_421730 := by decide
  rcases family_descends (prefixWord ++ tailWord_421730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421740 : List Nat := [2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 4]
def baseStart_421740 : Nat := 118140960795 + 421740 * 2 ^ 59
def prefixEnd_421740 : Nat := 4983230072969 + 3 ^ 40 * 421740 * 2
def baseEnd_421740 : Nat := 216555331227285174010459

theorem tailTrace_421740 : CollatzResearch.WordTrace tailWord_421740 prefixEnd_421740 216555331227285174010459 := by
  unfold tailWord_421740
  simp only [CollatzResearch.WordTrace]
  refine ⟨7691060746057741151355337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10254747661410321535140449 7691060746057741151355337)
  ·
    refine ⟨5768295559543305863516503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7691060746057741151355337 5768295559543305863516503)
    ·
      refine ⟨8652443339314958795274755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5768295559543305863516503 8652443339314958795274755)
      ·
        refine ⟨12978665008972438192912133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8652443339314958795274755 12978665008972438192912133)
        ·
          refine ⟨2433499689182332161171025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12978665008972438192912133 2433499689182332161171025)
          ·
            refine ⟨1825124766886749120878269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2433499689182332161171025 1825124766886749120878269)
            ·
              refine ⟨684421787582530920329351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1825124766886749120878269 684421787582530920329351)
              ·
                refine ⟨1026632681373796380494027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 684421787582530920329351 1026632681373796380494027)
                ·
                  refine ⟨1539949022060694570741041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1026632681373796380494027 1539949022060694570741041)
                  ·
                    refine ⟨1154961766545520928055781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1539949022060694570741041 1154961766545520928055781)
                    ·
                      refine ⟨216555331227285174010459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1154961766545520928055781 216555331227285174010459)
                      ·
                        rfl

theorem cell23_421740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 4].length) (baseStart_421740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421740 prefixEnd_421740 := by exact prefixLift 421740
  have htrace : WordTrace (prefixWord ++ tailWord_421740) baseStart_421740 baseEnd_421740 := by
    simpa [prefixWord, tailWord_421740, baseEnd_421740] using wordTrace_append hprefix tailTrace_421740
  have hstable : (prefixWord ++ tailWord_421740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421740).length < 2 ^ (prefixWord ++ tailWord_421740).sum := by decide
  have hdescent : baseEnd_421740 < baseStart_421740 := by decide
  rcases family_descends (prefixWord ++ tailWord_421740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421760 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 6, 1, 3]
def baseStart_421760 : Nat := 118140960795 + 421760 * 2 ^ 59
def prefixEnd_421760 : Nat := 4983230072969 + 3 ^ 40 * 421760 * 2
def baseEnd_421760 : Nat := 216565600840375095760367

theorem tailTrace_421760 : CollatzResearch.WordTrace tailWord_421760 prefixEnd_421760 216565600840375095760367 := by
  unfold tailWord_421760
  simp only [CollatzResearch.WordTrace]
  refine ⟨7691425476021512859219367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10255233968028683812292489 7691425476021512859219367)
  ·
    refine ⟨11537138214032269288829051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7691425476021512859219367 11537138214032269288829051)
    ·
      refine ⟨17305707321048403933243577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11537138214032269288829051 17305707321048403933243577)
      ·
        refine ⟨12979280490786302949932683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17305707321048403933243577 12979280490786302949932683)
        ·
          refine ⟨19468920736179454424899025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12979280490786302949932683 19468920736179454424899025)
          ·
            refine ⟨14601690552134590818674269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19468920736179454424899025 14601690552134590818674269)
            ·
              refine ⟨5475633957050471557002851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14601690552134590818674269 5475633957050471557002851)
              ·
                refine ⟨8213450935575707335504277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5475633957050471557002851 8213450935575707335504277)
                ·
                  refine ⟨385005512605111281351763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8213450935575707335504277 385005512605111281351763)
                  ·
                    refine ⟨577508268907666922027645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 385005512605111281351763 577508268907666922027645)
                    ·
                      refine ⟨216565600840375095760367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 577508268907666922027645 216565600840375095760367)
                      ·
                        rfl

theorem cell23_421760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 6, 1, 3].length) (baseStart_421760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421760 prefixEnd_421760 := by exact prefixLift 421760
  have htrace : WordTrace (prefixWord ++ tailWord_421760) baseStart_421760 baseEnd_421760 := by
    simpa [prefixWord, tailWord_421760, baseEnd_421760] using wordTrace_append hprefix tailTrace_421760
  have hstable : (prefixWord ++ tailWord_421760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421760).length < 2 ^ (prefixWord ++ tailWord_421760).sum := by decide
  have hdescent : baseEnd_421760 < baseStart_421760 := by decide
  rcases family_descends (prefixWord ++ tailWord_421760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421817 : List Nat := [1, 2, 1, 4, 2, 1, 3, 2, 1, 4, 2]
def baseStart_421817 : Nat := 118140960795 + 421817 * 2 ^ 59
def prefixEnd_421817 : Nat := 4983230072969 + 3 ^ 40 * 421817 * 2
def baseEnd_421817 : Nat := 216594869237681372747605

theorem tailTrace_421817 : CollatzResearch.WordTrace tailWord_421817 prefixEnd_421817 216594869237681372747605 := by
  unfold tailWord_421817
  simp only [CollatzResearch.WordTrace]
  refine ⟨15384929912836524453263705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10256619941891016302175803 15384929912836524453263705)
  ·
    refine ⟨11538697434627393339947779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15384929912836524453263705 11538697434627393339947779)
    ·
      refine ⟨17308046151941090009921669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11538697434627393339947779 17308046151941090009921669)
      ·
        refine ⟨3245258653488954376860313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17308046151941090009921669 3245258653488954376860313)
        ·
          refine ⟨2433943990116715782645235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3245258653488954376860313 2433943990116715782645235)
          ·
            refine ⟨3650915985175073673967853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2433943990116715782645235 3650915985175073673967853)
            ·
              refine ⟨1369093494440652627737945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3650915985175073673967853 1369093494440652627737945)
              ·
                refine ⟨1026820120830489470803459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1369093494440652627737945 1026820120830489470803459)
                ·
                  refine ⟨1540230181245734206205189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1026820120830489470803459 1540230181245734206205189)
                  ·
                    refine ⟨288793158983575163663473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1540230181245734206205189 288793158983575163663473)
                    ·
                      refine ⟨216594869237681372747605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 288793158983575163663473 216594869237681372747605)
                      ·
                        rfl

theorem cell23_421817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_421817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421817 prefixEnd_421817 := by exact prefixLift 421817
  have htrace : WordTrace (prefixWord ++ tailWord_421817) baseStart_421817 baseEnd_421817 := by
    simpa [prefixWord, tailWord_421817, baseEnd_421817] using wordTrace_append hprefix tailTrace_421817
  have hstable : (prefixWord ++ tailWord_421817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421817).length < 2 ^ (prefixWord ++ tailWord_421817).sum := by decide
  have hdescent : baseEnd_421817 < baseStart_421817 := by decide
  rcases family_descends (prefixWord ++ tailWord_421817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421821 : List Nat := [1, 4, 1, 2, 3, 2, 3, 1, 1, 3, 2]
def baseStart_421821 : Nat := 118140960795 + 421821 * 2 ^ 59
def prefixEnd_421821 : Nat := 4983230072969 + 3 ^ 40 * 421821 * 2
def baseEnd_421821 : Nat := 216596923160299357097587

theorem tailTrace_421821 : CollatzResearch.WordTrace tailWord_421821 prefixEnd_421821 216596923160299357097587 := by
  unfold tailWord_421821
  simp only [CollatzResearch.WordTrace]
  refine ⟨15385075804822033136409317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10256717203214688757606211 15385075804822033136409317)
  ·
    refine ⟨2884701713404131213076747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15385075804822033136409317 2884701713404131213076747)
    ·
      refine ⟨4327052570106196819615121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2884701713404131213076747 4327052570106196819615121)
      ·
        refine ⟨3245289427579647614711341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4327052570106196819615121 3245289427579647614711341)
        ·
          refine ⟨1216983535342367855516753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3245289427579647614711341 1216983535342367855516753)
          ·
            refine ⟨912737651506775891637565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1216983535342367855516753 912737651506775891637565)
            ·
              refine ⟨342276619315040959364087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 912737651506775891637565 342276619315040959364087)
              ·
                refine ⟨513414928972561439046131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 342276619315040959364087 513414928972561439046131)
                ·
                  refine ⟨770122393458842158569197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 513414928972561439046131 770122393458842158569197)
                  ·
                    refine ⟨288795897547065809463449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 770122393458842158569197 288795897547065809463449)
                    ·
                      refine ⟨216596923160299357097587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 288795897547065809463449 216596923160299357097587)
                      ·
                        rfl

theorem cell23_421821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_421821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421821 prefixEnd_421821 := by exact prefixLift 421821
  have htrace : WordTrace (prefixWord ++ tailWord_421821) baseStart_421821 baseEnd_421821 := by
    simpa [prefixWord, tailWord_421821, baseEnd_421821] using wordTrace_append hprefix tailTrace_421821
  have hstable : (prefixWord ++ tailWord_421821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421821).length < 2 ^ (prefixWord ++ tailWord_421821).sum := by decide
  have hdescent : baseEnd_421821 < baseStart_421821 := by decide
  rcases family_descends (prefixWord ++ tailWord_421821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421834 : List Nat := [3, 1, 2, 1, 2, 1, 3, 4, 2, 2, 2]
def baseStart_421834 : Nat := 118140960795 + 421834 * 2 ^ 59
def prefixEnd_421834 : Nat := 4983230072969 + 3 ^ 40 * 421834 * 2
def baseEnd_421834 : Nat := 216603598408807806235027

theorem tailTrace_421834 : CollatzResearch.WordTrace tailWord_421834 prefixEnd_421834 216603598408807806235027 := by
  unfold tailWord_421834
  simp only [CollatzResearch.WordTrace]
  refine ⟨3846387488443734089158139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10257033302516624237755037 3846387488443734089158139)
  ·
    refine ⟨5769581232665601133737209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3846387488443734089158139 5769581232665601133737209)
    ·
      refine ⟨4327185924499200850302907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5769581232665601133737209 4327185924499200850302907)
      ·
        refine ⟨6490778886748801275454361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4327185924499200850302907 6490778886748801275454361)
        ·
          refine ⟨4868084165061600956590771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6490778886748801275454361 4868084165061600956590771)
          ·
            refine ⟨7302126247592401434886157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4868084165061600956590771 7302126247592401434886157)
            ·
              refine ⟨2738297342847150538082309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7302126247592401434886157 2738297342847150538082309)
              ·
                refine ⟨513430751783840725890433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2738297342847150538082309 513430751783840725890433)
                ·
                  refine ⟨385073063837880544417825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 513430751783840725890433 385073063837880544417825)
                  ·
                    refine ⟨288804797878410408313369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 385073063837880544417825 288804797878410408313369)
                    ·
                      refine ⟨216603598408807806235027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 288804797878410408313369 216603598408807806235027)
                      ·
                        rfl

theorem cell23_421834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 2, 2, 2].length) (baseStart_421834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421834 prefixEnd_421834 := by exact prefixLift 421834
  have htrace : WordTrace (prefixWord ++ tailWord_421834) baseStart_421834 baseEnd_421834 := by
    simpa [prefixWord, tailWord_421834, baseEnd_421834] using wordTrace_append hprefix tailTrace_421834
  have hstable : (prefixWord ++ tailWord_421834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421834).length < 2 ^ (prefixWord ++ tailWord_421834).sum := by decide
  have hdescent : baseEnd_421834 < baseStart_421834 := by decide
  rcases family_descends (prefixWord ++ tailWord_421834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421907 : List Nat := [1, 1, 1, 2, 1, 4, 4, 1, 2, 4, 2]
def baseStart_421907 : Nat := 118140960795 + 421907 * 2 ^ 59
def prefixEnd_421907 : Nat := 4983230072969 + 3 ^ 40 * 421907 * 2
def baseEnd_421907 : Nat := 216641082496586020622191

theorem tailTrace_421907 : CollatzResearch.WordTrace tailWord_421907 prefixEnd_421907 216641082496586020622191 := by
  unfold tailWord_421907
  simp only [CollatzResearch.WordTrace]
  refine ⟨15388212482510469824039975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10258808321673646549359983 15388212482510469824039975)
  ·
    refine ⟨23082318723765704736059963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15388212482510469824039975 23082318723765704736059963)
    ·
      refine ⟨34623478085648557104089945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23082318723765704736059963 34623478085648557104089945)
      ·
        refine ⟨25967608564236417828067459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34623478085648557104089945 25967608564236417828067459)
        ·
          refine ⟨38951412846354626742101189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25967608564236417828067459 38951412846354626742101189)
          ·
            refine ⟨7303389908691492514143973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38951412846354626742101189 7303389908691492514143973)
            ·
              refine ⟨1369385607879654846401995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7303389908691492514143973 1369385607879654846401995)
              ·
                refine ⟨2054078411819482269602993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1369385607879654846401995 2054078411819482269602993)
                ·
                  refine ⟨1540558808864611702202245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2054078411819482269602993 1540558808864611702202245)
                  ·
                    refine ⟨288854776662114694162921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1540558808864611702202245 288854776662114694162921)
                    ·
                      refine ⟨216641082496586020622191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 288854776662114694162921 216641082496586020622191)
                      ·
                        rfl

theorem cell23_421907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 4, 2].length) (baseStart_421907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421907 prefixEnd_421907 := by exact prefixLift 421907
  have htrace : WordTrace (prefixWord ++ tailWord_421907) baseStart_421907 baseEnd_421907 := by
    simpa [prefixWord, tailWord_421907, baseEnd_421907] using wordTrace_append hprefix tailTrace_421907
  have hstable : (prefixWord ++ tailWord_421907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421907).length < 2 ^ (prefixWord ++ tailWord_421907).sum := by decide
  have hdescent : baseEnd_421907 < baseStart_421907 := by decide
  rcases family_descends (prefixWord ++ tailWord_421907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421944 : List Nat := [2, 1, 2, 1, 6, 1, 1, 2, 2, 2, 3]
def baseStart_421944 : Nat := 118140960795 + 421944 * 2 ^ 59
def prefixEnd_421944 : Nat := 4983230072969 + 3 ^ 40 * 421944 * 2
def baseEnd_421944 : Nat := 216660081280802375859521

theorem tailTrace_421944 : CollatzResearch.WordTrace tailWord_421944 prefixEnd_421944 216660081280802375859521 := by
  unfold tailWord_421944
  simp only [CollatzResearch.WordTrace]
  refine ⟨7694780991688212571568443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10259707988917616762091257 7694780991688212571568443)
  ·
    refine ⟨11542171487532318857352665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7694780991688212571568443 11542171487532318857352665)
    ·
      refine ⟨8656628615649239143014499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11542171487532318857352665 8656628615649239143014499)
      ·
        refine ⟨12984942923473858714521749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8656628615649239143014499 12984942923473858714521749)
        ·
          refine ⟨608669199537837127243207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12984942923473858714521749 608669199537837127243207)
          ·
            refine ⟨913003799306755690864811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 608669199537837127243207 913003799306755690864811)
            ·
              refine ⟨1369505698960133536297217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 913003799306755690864811 1369505698960133536297217)
              ·
                refine ⟨1027129274220100152222913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1369505698960133536297217 1027129274220100152222913)
                ·
                  refine ⟨770346955665075114167185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1027129274220100152222913 770346955665075114167185)
                  ·
                    refine ⟨577760216748806335625389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 770346955665075114167185 577760216748806335625389)
                    ·
                      refine ⟨216660081280802375859521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 577760216748806335625389 216660081280802375859521)
                      ·
                        rfl

theorem cell23_421944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 2, 2, 2, 3].length) (baseStart_421944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421944 prefixEnd_421944 := by exact prefixLift 421944
  have htrace : WordTrace (prefixWord ++ tailWord_421944) baseStart_421944 baseEnd_421944 := by
    simpa [prefixWord, tailWord_421944, baseEnd_421944] using wordTrace_append hprefix tailTrace_421944
  have hstable : (prefixWord ++ tailWord_421944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421944).length < 2 ^ (prefixWord ++ tailWord_421944).sum := by decide
  have hdescent : baseEnd_421944 < baseStart_421944 := by decide
  rcases family_descends (prefixWord ++ tailWord_421944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421984 : List Nat := [2, 1, 1, 3, 2, 3, 1, 3, 2, 3, 2]
def baseStart_421984 : Nat := 118140960795 + 421984 * 2 ^ 59
def prefixEnd_421984 : Nat := 4983230072969 + 3 ^ 40 * 421984 * 2
def baseEnd_421984 : Nat := 216680620506982219359337

theorem tailTrace_421984 : CollatzResearch.WordTrace tailWord_421984 prefixEnd_421984 216680620506982219359337 := by
  unfold tailWord_421984
  simp only [CollatzResearch.WordTrace]
  refine ⟨7695510451615755987296503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10260680602154341316395337 7695510451615755987296503)
  ·
    refine ⟨11543265677423633980944755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7695510451615755987296503 11543265677423633980944755)
    ·
      refine ⟨17314898516135450971417133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11543265677423633980944755 17314898516135450971417133)
      ·
        refine ⟨6493086943550794114281425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17314898516135450971417133 6493086943550794114281425)
        ·
          refine ⟨4869815207663095585711069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6493086943550794114281425 4869815207663095585711069)
          ·
            refine ⟨1826180702873660844641651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4869815207663095585711069 1826180702873660844641651)
            ·
              refine ⟨2739271054310491266962477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1826180702873660844641651 2739271054310491266962477)
              ·
                refine ⟨1027226645366434225110929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2739271054310491266962477 1027226645366434225110929)
                ·
                  refine ⟨770419984024825668833197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1027226645366434225110929 770419984024825668833197)
                  ·
                    refine ⟨288907494009309625812449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 770419984024825668833197 288907494009309625812449)
                    ·
                      refine ⟨216680620506982219359337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 288907494009309625812449 216680620506982219359337)
                      ·
                        rfl

theorem cell23_421984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 2, 3, 2].length) (baseStart_421984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421984 prefixEnd_421984 := by exact prefixLift 421984
  have htrace : WordTrace (prefixWord ++ tailWord_421984) baseStart_421984 baseEnd_421984 := by
    simpa [prefixWord, tailWord_421984, baseEnd_421984] using wordTrace_append hprefix tailTrace_421984
  have hstable : (prefixWord ++ tailWord_421984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421984).length < 2 ^ (prefixWord ++ tailWord_421984).sum := by decide
  have hdescent : baseEnd_421984 < baseStart_421984 := by decide
  rcases family_descends (prefixWord ++ tailWord_421984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_421991 : List Nat := [1, 1, 5, 1, 1, 2, 2, 5, 1, 1, 3]
def baseStart_421991 : Nat := 118140960795 + 421991 * 2 ^ 59
def prefixEnd_421991 : Nat := 4983230072969 + 3 ^ 40 * 421991 * 2
def baseEnd_421991 : Nat := 216684214871563691971805

theorem tailTrace_421991 : CollatzResearch.WordTrace tailWord_421991 prefixEnd_421991 216684214871563691971805 := by
  unfold tailWord_421991
  simp only [CollatzResearch.WordTrace]
  refine ⟨15391276214206152170097827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10260850809470768113398551 15391276214206152170097827)
  ·
    refine ⟨23086914321309228255146741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15391276214206152170097827 23086914321309228255146741)
    ·
      refine ⟨2164398217622740148920007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23086914321309228255146741 2164398217622740148920007)
      ·
        refine ⟨3246597326434110223380011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2164398217622740148920007 3246597326434110223380011)
        ·
          refine ⟨4869895989651165335070017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3246597326434110223380011 4869895989651165335070017)
          ·
            refine ⟨3652421992238374001302513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4869895989651165335070017 3652421992238374001302513)
            ·
              refine ⟨2739316494178780500976885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3652421992238374001302513 2739316494178780500976885)
              ·
                refine ⟨256810921329260671966583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2739316494178780500976885 256810921329260671966583)
                ·
                  refine ⟨385216381993891007949875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 256810921329260671966583 385216381993891007949875)
                  ·
                    refine ⟨577824572990836511924813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 385216381993891007949875 577824572990836511924813)
                    ·
                      refine ⟨216684214871563691971805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 577824572990836511924813 216684214871563691971805)
                      ·
                        rfl

theorem cell23_421991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 5, 1, 1, 3].length) (baseStart_421991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_421991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_421991 prefixEnd_421991 := by exact prefixLift 421991
  have htrace : WordTrace (prefixWord ++ tailWord_421991) baseStart_421991 baseEnd_421991 := by
    simpa [prefixWord, tailWord_421991, baseEnd_421991] using wordTrace_append hprefix tailTrace_421991
  have hstable : (prefixWord ++ tailWord_421991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_421991).length < 2 ^ (prefixWord ++ tailWord_421991).sum := by decide
  have hdescent : baseEnd_421991 < baseStart_421991 := by decide
  rcases family_descends (prefixWord ++ tailWord_421991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422024 : List Nat := [2, 1, 3, 4, 1, 2, 2, 1, 1, 6]
def baseStart_422024 : Nat := 118140960795 + 422024 * 2 ^ 59
def prefixEnd_422024 : Nat := 4983230072969 + 3 ^ 40 * 422024 * 2
def baseEnd_422024 : Nat := 72233719911054020953051

theorem tailTrace_422024 : CollatzResearch.WordTrace tailWord_422024 prefixEnd_422024 72233719911054020953051 := by
  unfold tailWord_422024
  simp only [CollatzResearch.WordTrace]
  refine ⟨7696239911543299403024563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10261653215391065870699417 7696239911543299403024563)
  ·
    refine ⟨11544359867314949104536845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7696239911543299403024563 11544359867314949104536845)
    ·
      refine ⟨4329134950243105914201317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11544359867314949104536845 4329134950243105914201317)
      ·
        refine ⟨811712803170582358912747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4329134950243105914201317 811712803170582358912747)
        ·
          refine ⟨1217569204755873538369121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 811712803170582358912747 1217569204755873538369121)
          ·
            refine ⟨913176903566905153776841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1217569204755873538369121 913176903566905153776841)
            ·
              refine ⟨684882677675178865332631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 913176903566905153776841 684882677675178865332631)
              ·
                refine ⟨1027324016512768297998947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 684882677675178865332631 1027324016512768297998947)
                ·
                  refine ⟨1540986024769152446998421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1027324016512768297998947 1540986024769152446998421)
                  ·
                    refine ⟨72233719911054020953051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1540986024769152446998421 72233719911054020953051)
                    ·
                      rfl

theorem cell23_422024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 1, 6].length) (baseStart_422024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422024 prefixEnd_422024 := by exact prefixLift 422024
  have htrace : WordTrace (prefixWord ++ tailWord_422024) baseStart_422024 baseEnd_422024 := by
    simpa [prefixWord, tailWord_422024, baseEnd_422024] using wordTrace_append hprefix tailTrace_422024
  have hstable : (prefixWord ++ tailWord_422024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422024).length < 2 ^ (prefixWord ++ tailWord_422024).sum := by decide
  have hdescent : baseEnd_422024 < baseStart_422024 := by decide
  rcases family_descends (prefixWord ++ tailWord_422024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422034 : List Nat := [3, 2, 3, 1, 1, 1, 1, 3, 3, 2, 3]
def baseStart_422034 : Nat := 118140960795 + 422034 * 2 ^ 59
def prefixEnd_422034 : Nat := 4983230072969 + 3 ^ 40 * 422034 * 2
def baseEnd_422034 : Nat := 216706294539707023734107

theorem tailTrace_422034 : CollatzResearch.WordTrace tailWord_422034 prefixEnd_422034 216706294539707023734107 := by
  unfold tailWord_422034
  simp only [CollatzResearch.WordTrace]
  refine ⟨3848211138262592628478289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10261896368700247009275437 3848211138262592628478289)
  ·
    refine ⟨2886158353696944471358717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3848211138262592628478289 2886158353696944471358717)
    ·
      refine ⟨1082309382636354176759519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2886158353696944471358717 1082309382636354176759519)
      ·
        refine ⟨1623464073954531265139279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1082309382636354176759519 1623464073954531265139279)
        ·
          refine ⟨2435196110931796897708919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1623464073954531265139279 2435196110931796897708919)
          ·
            refine ⟨3652794166397695346563379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2435196110931796897708919 3652794166397695346563379)
            ·
              refine ⟨5479191249596543019845069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3652794166397695346563379 5479191249596543019845069)
              ·
                refine ⟨2054696718598703632441901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5479191249596543019845069 2054696718598703632441901)
                ·
                  refine ⟨770511269474513862165713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2054696718598703632441901 770511269474513862165713)
                  ·
                    refine ⟨577883452105885396624285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 770511269474513862165713 577883452105885396624285)
                    ·
                      refine ⟨216706294539707023734107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 577883452105885396624285 216706294539707023734107)
                      ·
                        rfl

theorem cell23_422034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_422034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422034 prefixEnd_422034 := by exact prefixLift 422034
  have htrace : WordTrace (prefixWord ++ tailWord_422034) baseStart_422034 baseEnd_422034 := by
    simpa [prefixWord, tailWord_422034, baseEnd_422034] using wordTrace_append hprefix tailTrace_422034
  have hstable : (prefixWord ++ tailWord_422034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422034).length < 2 ^ (prefixWord ++ tailWord_422034).sum := by decide
  have hdescent : baseEnd_422034 < baseStart_422034 := by decide
  rcases family_descends (prefixWord ++ tailWord_422034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422037 : List Nat := [1, 3, 2, 1, 1, 1, 7, 7]
def baseStart_422037 : Nat := 118140960795 + 422037 * 2 ^ 59
def prefixEnd_422037 : Nat := 4983230072969 + 3 ^ 40 * 422037 * 2
def baseEnd_422037 : Nat := 8026216110432241185059

theorem tailTrace_422037 : CollatzResearch.WordTrace tailWord_422037 prefixEnd_422037 8026216110432241185059 := by
  unfold tailWord_422037
  simp only [CollatzResearch.WordTrace]
  refine ⟨15392953972039502026272365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10261969314693001350848243 15392953972039502026272365)
  ·
    refine ⟨5772357739514813259852137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15392953972039502026272365 5772357739514813259852137)
    ·
      refine ⟨4329268304636109944889103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5772357739514813259852137 4329268304636109944889103)
      ·
        refine ⟨6493902456954164917333655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4329268304636109944889103 6493902456954164917333655)
        ·
          refine ⟨9740853685431247376000483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6493902456954164917333655 9740853685431247376000483)
          ·
            refine ⟨14611280528146871064000725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9740853685431247376000483 14611280528146871064000725)
            ·
              refine ⟨342451887378442290562517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 14611280528146871064000725 342451887378442290562517)
              ·
                refine ⟨8026216110432241185059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 342451887378442290562517 8026216110432241185059)
                ·
                  rfl

theorem cell23_422037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 7].length) (baseStart_422037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422037 prefixEnd_422037 := by exact prefixLift 422037
  have htrace : WordTrace (prefixWord ++ tailWord_422037) baseStart_422037 baseEnd_422037 := by
    simpa [prefixWord, tailWord_422037, baseEnd_422037] using wordTrace_append hprefix tailTrace_422037
  have hstable : (prefixWord ++ tailWord_422037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422037).length < 2 ^ (prefixWord ++ tailWord_422037).sum := by decide
  have hdescent : baseEnd_422037 < baseStart_422037 := by decide
  rcases family_descends (prefixWord ++ tailWord_422037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422048 : List Nat := [2, 1, 1, 4, 2, 2, 1, 5, 1, 2, 2]
def baseStart_422048 : Nat := 118140960795 + 422048 * 2 ^ 59
def prefixEnd_422048 : Nat := 4983230072969 + 3 ^ 40 * 422048 * 2
def baseEnd_422048 : Nat := 216713483268869968959043

theorem tailTrace_422048 : CollatzResearch.WordTrace tailWord_422048 prefixEnd_422048 216713483268869968959043 := by
  unfold tailWord_422048
  simp only [CollatzResearch.WordTrace]
  refine ⟨7696677587499825452461399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10262236783333100603281865 7696677587499825452461399)
  ·
    refine ⟨11545016381249738178692099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7696677587499825452461399 11545016381249738178692099)
    ·
      refine ⟨17317524571874607268038149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11545016381249738178692099 17317524571874607268038149)
      ·
        refine ⟨3247035857226488862757153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17317524571874607268038149 3247035857226488862757153)
        ·
          refine ⟨2435276892919866647067865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3247035857226488862757153 2435276892919866647067865)
          ·
            refine ⟨1826457669689899985300899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2435276892919866647067865 1826457669689899985300899)
            ·
              refine ⟨2739686504534849977951349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1826457669689899985300899 2739686504534849977951349)
              ·
                refine ⟨256845609800142185432939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2739686504534849977951349 256845609800142185432939)
                ·
                  refine ⟨385268414700213278149409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 256845609800142185432939 385268414700213278149409)
                  ·
                    refine ⟨288951311025159958612057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 385268414700213278149409 288951311025159958612057)
                    ·
                      refine ⟨216713483268869968959043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 288951311025159958612057 216713483268869968959043)
                      ·
                        rfl

theorem cell23_422048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 5, 1, 2, 2].length) (baseStart_422048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422048 prefixEnd_422048 := by exact prefixLift 422048
  have htrace : WordTrace (prefixWord ++ tailWord_422048) baseStart_422048 baseEnd_422048 := by
    simpa [prefixWord, tailWord_422048, baseEnd_422048] using wordTrace_append hprefix tailTrace_422048
  have hstable : (prefixWord ++ tailWord_422048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422048).length < 2 ^ (prefixWord ++ tailWord_422048).sum := by decide
  have hdescent : baseEnd_422048 < baseStart_422048 := by decide
  rcases family_descends (prefixWord ++ tailWord_422048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422074 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 5, 3, 2]
def baseStart_422074 : Nat := 118140960795 + 422074 * 2 ^ 59
def prefixEnd_422074 : Nat := 4983230072969 + 3 ^ 40 * 422074 * 2
def baseEnd_422074 : Nat := 216726833765886867233923

theorem tailTrace_422074 : CollatzResearch.WordTrace tailWord_422074 prefixEnd_422074 216726833765886867233923 := by
  unfold tailWord_422074
  simp only [CollatzResearch.WordTrace]
  refine ⟨3848575868226364336342319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10262868981936971563579517 3848575868226364336342319)
  ·
    refine ⟨5772863802339546504513479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3848575868226364336342319 5772863802339546504513479)
    ·
      refine ⟨8659295703509319756770219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5772863802339546504513479 8659295703509319756770219)
      ·
        refine ⟨12988943555263979635155329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8659295703509319756770219 12988943555263979635155329)
        ·
          refine ⟨9741707666447984726366497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12988943555263979635155329 9741707666447984726366497)
          ·
            refine ⟨7306280749835988544774873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9741707666447984726366497 7306280749835988544774873)
            ·
              refine ⟨5479710562376991408581155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7306280749835988544774873 5479710562376991408581155)
              ·
                refine ⟨8219565843565487112871733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5479710562376991408581155 8219565843565487112871733)
                ·
                  refine ⟨770584297834264416831725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8219565843565487112871733 770584297834264416831725)
                  ·
                    refine ⟨288969111687849156311897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 770584297834264416831725 288969111687849156311897)
                    ·
                      refine ⟨216726833765886867233923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 288969111687849156311897 216726833765886867233923)
                      ·
                        rfl

theorem cell23_422074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 5, 3, 2].length) (baseStart_422074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422074 prefixEnd_422074 := by exact prefixLift 422074
  have htrace : WordTrace (prefixWord ++ tailWord_422074) baseStart_422074 baseEnd_422074 := by
    simpa [prefixWord, tailWord_422074, baseEnd_422074] using wordTrace_append hprefix tailTrace_422074
  have hstable : (prefixWord ++ tailWord_422074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422074).length < 2 ^ (prefixWord ++ tailWord_422074).sum := by decide
  have hdescent : baseEnd_422074 < baseStart_422074 := by decide
  rcases family_descends (prefixWord ++ tailWord_422074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422078 : List Nat := [4, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4]
def baseStart_422078 : Nat := 118140960795 + 422078 * 2 ^ 59
def prefixEnd_422078 : Nat := 4983230072969 + 3 ^ 40 * 422078 * 2
def baseEnd_422078 : Nat := 216728887688504851583905

theorem tailTrace_422078 : CollatzResearch.WordTrace tailWord_422078 prefixEnd_422078 216728887688504851583905 := by
  unfold tailWord_422078
  simp only [CollatzResearch.WordTrace]
  refine ⟨1924306170611370753564361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10262966243260644019009925 1924306170611370753564361)
  ·
    refine ⟨1443229627958528065173271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1924306170611370753564361 1443229627958528065173271)
    ·
      refine ⟨2164844441937792097759907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1443229627958528065173271 2164844441937792097759907)
      ·
        refine ⟨3247266662906688146639861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2164844441937792097759907 3247266662906688146639861)
        ·
          refine ⟨304431249647502013747487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3247266662906688146639861 304431249647502013747487)
          ·
            refine ⟨456646874471253020621231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304431249647502013747487 456646874471253020621231)
            ·
              refine ⟨684970311706879530931847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 456646874471253020621231 684970311706879530931847)
              ·
                refine ⟨1027455467560319296397771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 684970311706879530931847 1027455467560319296397771)
                ·
                  refine ⟨1541183201340478944596657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1027455467560319296397771 1541183201340478944596657)
                  ·
                    refine ⟨1155887401005359208447493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1541183201340478944596657 1155887401005359208447493)
                    ·
                      refine ⟨216728887688504851583905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1155887401005359208447493 216728887688504851583905)
                      ·
                        rfl

theorem cell23_422078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_422078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422078 prefixEnd_422078 := by exact prefixLift 422078
  have htrace : WordTrace (prefixWord ++ tailWord_422078) baseStart_422078 baseEnd_422078 := by
    simpa [prefixWord, tailWord_422078, baseEnd_422078] using wordTrace_append hprefix tailTrace_422078
  have hstable : (prefixWord ++ tailWord_422078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422078).length < 2 ^ (prefixWord ++ tailWord_422078).sum := by decide
  have hdescent : baseEnd_422078 < baseStart_422078 := by decide
  rcases family_descends (prefixWord ++ tailWord_422078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422091 : List Nat := [1, 1, 1, 1, 3, 2, 6, 2, 1, 3, 2]
def baseStart_422091 : Nat := 118140960795 + 422091 * 2 ^ 59
def prefixEnd_422091 : Nat := 4983230072969 + 3 ^ 40 * 422091 * 2
def baseEnd_422091 : Nat := 216735562937013300721345

theorem tailTrace_422091 : CollatzResearch.WordTrace tailWord_422091 prefixEnd_422091 216735562937013300721345 := by
  unfold tailWord_422091
  simp only [CollatzResearch.WordTrace]
  refine ⟨15394923513843869248738127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10263282342562579499158751 15394923513843869248738127)
  ·
    refine ⟨23092385270765803873107191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15394923513843869248738127 23092385270765803873107191)
    ·
      refine ⟨34638577906148705809660787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23092385270765803873107191 34638577906148705809660787)
      ·
        refine ⟨51957866859223058714491181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34638577906148705809660787 51957866859223058714491181)
        ·
          refine ⟨19484200072208647017934193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51957866859223058714491181 19484200072208647017934193)
          ·
            refine ⟨14613150054156485263450645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19484200072208647017934193 14613150054156485263450645)
            ·
              refine ⟨684991408788585246724249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14613150054156485263450645 684991408788585246724249)
              ·
                refine ⟨513743556591438935043187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 684991408788585246724249 513743556591438935043187)
                ·
                  refine ⟨770615334887158402564781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 513743556591438935043187 770615334887158402564781)
                  ·
                    refine ⟨288980750582684400961793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 770615334887158402564781 288980750582684400961793)
                    ·
                      refine ⟨216735562937013300721345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 288980750582684400961793 216735562937013300721345)
                      ·
                        rfl

theorem cell23_422091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 3, 2].length) (baseStart_422091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422091 prefixEnd_422091 := by exact prefixLift 422091
  have htrace : WordTrace (prefixWord ++ tailWord_422091) baseStart_422091 baseEnd_422091 := by
    simpa [prefixWord, tailWord_422091, baseEnd_422091] using wordTrace_append hprefix tailTrace_422091
  have hstable : (prefixWord ++ tailWord_422091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422091).length < 2 ^ (prefixWord ++ tailWord_422091).sum := by decide
  have hdescent : baseEnd_422091 < baseStart_422091 := by decide
  rcases family_descends (prefixWord ++ tailWord_422091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422134 : List Nat := [5, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4]
def baseStart_422134 : Nat := 118140960795 + 422134 * 2 ^ 59
def prefixEnd_422134 : Nat := 4983230072969 + 3 ^ 40 * 422134 * 2
def baseEnd_422134 : Nat := 216757642605156632483647

theorem tailTrace_422134 : CollatzResearch.WordTrace tailWord_422134 prefixEnd_422134 216757642605156632483647 := by
  unfold tailWord_422134
  simp only [CollatzResearch.WordTrace]
  refine ⟨962280740793005474534591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10264327901792058395035637 962280740793005474534591)
  ·
    refine ⟨1443421111189508211801887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 962280740793005474534591 1443421111189508211801887)
    ·
      refine ⟨2165131666784262317702831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1443421111189508211801887 2165131666784262317702831)
      ·
        refine ⟨3247697500176393476554247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2165131666784262317702831 3247697500176393476554247)
        ·
          refine ⟨4871546250264590214831371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3247697500176393476554247 4871546250264590214831371)
          ·
            refine ⟨7307319375396885322247057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4871546250264590214831371 7307319375396885322247057)
            ·
              refine ⟨5480489531547663991685293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7307319375396885322247057 5480489531547663991685293)
              ·
                refine ⟨2055183574330373996881985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5480489531547663991685293 2055183574330373996881985)
                ·
                  refine ⟨1541387680747780497661489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2055183574330373996881985 1541387680747780497661489)
                  ·
                    refine ⟨1156040760560835373246117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1541387680747780497661489 1156040760560835373246117)
                    ·
                      refine ⟨216757642605156632483647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1156040760560835373246117 216757642605156632483647)
                      ·
                        rfl

theorem cell23_422134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_422134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422134 prefixEnd_422134 := by exact prefixLift 422134
  have htrace : WordTrace (prefixWord ++ tailWord_422134) baseStart_422134 baseEnd_422134 := by
    simpa [prefixWord, tailWord_422134, baseEnd_422134] using wordTrace_append hprefix tailTrace_422134
  have hstable : (prefixWord ++ tailWord_422134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422134).length < 2 ^ (prefixWord ++ tailWord_422134).sum := by decide
  have hdescent : baseEnd_422134 < baseStart_422134 := by decide
  rcases family_descends (prefixWord ++ tailWord_422134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422138 : List Nat := [3, 1, 1, 1, 1, 6, 1, 3, 2, 2, 2]
def baseStart_422138 : Nat := 118140960795 + 422138 * 2 ^ 59
def prefixEnd_422138 : Nat := 4983230072969 + 3 ^ 40 * 422138 * 2
def baseEnd_422138 : Nat := 216759696527774616833629

theorem tailTrace_422138 : CollatzResearch.WordTrace tailWord_422138 prefixEnd_422138 216759696527774616833629 := by
  unfold tailWord_422138
  simp only [CollatzResearch.WordTrace]
  refine ⟨3849159436168399068924767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10264425163115730850466045 3849159436168399068924767)
  ·
    refine ⟨5773739154252598603387151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3849159436168399068924767 5773739154252598603387151)
    ·
      refine ⟨8660608731378897905080727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5773739154252598603387151 8660608731378897905080727)
      ·
        refine ⟨12990913097068346857621091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8660608731378897905080727 12990913097068346857621091)
        ·
          refine ⟨19486369645602520286431637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12990913097068346857621091 19486369645602520286431637)
          ·
            refine ⟨913423577137618138426483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19486369645602520286431637 913423577137618138426483)
            ·
              refine ⟨1370135365706427207639725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 913423577137618138426483 1370135365706427207639725)
              ·
                refine ⟨513800762139910202864897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1370135365706427207639725 513800762139910202864897)
                ·
                  refine ⟨385350571604932652148673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 513800762139910202864897 385350571604932652148673)
                  ·
                    refine ⟨289012928703699489111505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 385350571604932652148673 289012928703699489111505)
                    ·
                      refine ⟨216759696527774616833629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 289012928703699489111505 216759696527774616833629)
                      ·
                        rfl

theorem cell23_422138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 2, 2, 2].length) (baseStart_422138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422138 prefixEnd_422138 := by exact prefixLift 422138
  have htrace : WordTrace (prefixWord ++ tailWord_422138) baseStart_422138 baseEnd_422138 := by
    simpa [prefixWord, tailWord_422138, baseEnd_422138] using wordTrace_append hprefix tailTrace_422138
  have hstable : (prefixWord ++ tailWord_422138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422138).length < 2 ^ (prefixWord ++ tailWord_422138).sum := by decide
  have hdescent : baseEnd_422138 < baseStart_422138 := by decide
  rcases family_descends (prefixWord ++ tailWord_422138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422178 : List Nat := [3, 3, 1, 1, 3, 1, 4, 2, 5]
def baseStart_422178 : Nat := 118140960795 + 422178 * 2 ^ 59
def prefixEnd_422178 : Nat := 4983230072969 + 3 ^ 40 * 422178 * 2
def baseEnd_422178 : Nat := 24086692861550495592605

theorem tailTrace_422178 : CollatzResearch.WordTrace tailWord_422178 prefixEnd_422178 24086692861550495592605 := by
  unfold tailWord_422178
  simp only [CollatzResearch.WordTrace]
  refine ⟨3849524166132170776788797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10265397776352455404770125 3849524166132170776788797)
  ·
    refine ⟨1443571562299564041295799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3849524166132170776788797 1443571562299564041295799)
    ·
      refine ⟨2165357343449346061943699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1443571562299564041295799 2165357343449346061943699)
      ·
        refine ⟨3248036015174019092915549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2165357343449346061943699 3248036015174019092915549)
        ·
          refine ⟨1218013505690257159843331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3248036015174019092915549 1218013505690257159843331)
          ·
            refine ⟨1827020258535385739764997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1218013505690257159843331 1827020258535385739764997)
            ·
              refine ⟨342566298475384826205937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1827020258535385739764997 342566298475384826205937)
              ·
                refine ⟨256924723856538619654453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 342566298475384826205937 256924723856538619654453)
                ·
                  refine ⟨24086692861550495592605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 256924723856538619654453 24086692861550495592605)
                  ·
                    rfl

theorem cell23_422178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_422178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422178 prefixEnd_422178 := by exact prefixLift 422178
  have htrace : WordTrace (prefixWord ++ tailWord_422178) baseStart_422178 baseEnd_422178 := by
    simpa [prefixWord, tailWord_422178, baseEnd_422178] using wordTrace_append hprefix tailTrace_422178
  have hstable : (prefixWord ++ tailWord_422178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422178).length < 2 ^ (prefixWord ++ tailWord_422178).sum := by decide
  have hdescent : baseEnd_422178 < baseStart_422178 := by decide
  rcases family_descends (prefixWord ++ tailWord_422178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422217 : List Nat := [1, 2, 1, 1, 2, 3, 1, 4, 8]
def baseStart_422217 : Nat := 118140960795 + 422217 * 2 ^ 59
def prefixEnd_422217 : Nat := 4983230072969 + 3 ^ 40 * 422217 * 2
def baseEnd_422217 : Nat := 24088917944386645305085

theorem tailTrace_422217 : CollatzResearch.WordTrace tailWord_422217 prefixEnd_422217 24088917944386645305085 := by
  unfold tailWord_422217
  simp only [CollatzResearch.WordTrace]
  refine ⟨15399519111387392767824905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10266346074258261845216603 15399519111387392767824905)
  ·
    refine ⟨11549639333540544575868679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15399519111387392767824905 11549639333540544575868679)
    ·
      refine ⟨17324459000310816863803019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11549639333540544575868679 17324459000310816863803019)
      ·
        refine ⟨25986688500466225295704529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17324459000310816863803019 25986688500466225295704529)
        ·
          refine ⟨19490016375349668971778397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25986688500466225295704529 19490016375349668971778397)
          ·
            refine ⟨7308756140756125864416899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19490016375349668971778397 7308756140756125864416899)
            ·
              refine ⟨10963134211134188796625349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7308756140756125864416899 10963134211134188796625349)
              ·
                refine ⟨2055587664587660399367253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10963134211134188796625349 2055587664587660399367253)
                ·
                  refine ⟨24088917944386645305085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2055587664587660399367253 24088917944386645305085)
                  ·
                    rfl

theorem cell23_422217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 8].length) (baseStart_422217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422217 prefixEnd_422217 := by exact prefixLift 422217
  have htrace : WordTrace (prefixWord ++ tailWord_422217) baseStart_422217 baseEnd_422217 := by
    simpa [prefixWord, tailWord_422217, baseEnd_422217] using wordTrace_append hprefix tailTrace_422217
  have hstable : (prefixWord ++ tailWord_422217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422217).length < 2 ^ (prefixWord ++ tailWord_422217).sum := by decide
  have hdescent : baseEnd_422217 < baseStart_422217 := by decide
  rcases family_descends (prefixWord ++ tailWord_422217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422281 : List Nat := [1, 2, 1, 1, 6, 1, 2, 3, 1, 5]
def baseStart_422281 : Nat := 118140960795 + 422281 * 2 ^ 59
def prefixEnd_422281 : Nat := 4983230072969 + 3 ^ 40 * 422281 * 2
def baseEnd_422281 : Nat := 72277708087122519115157

theorem tailTrace_422281 : CollatzResearch.WordTrace tailWord_422281 prefixEnd_422281 72277708087122519115157 := by
  unfold tailWord_422281
  simp only [CollatzResearch.WordTrace]
  refine ⟨15401853383155531698154697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10267902255437021132103131 15401853383155531698154697)
  ·
    refine ⟨11551390037366648773616023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15401853383155531698154697 11551390037366648773616023)
    ·
      refine ⟨17327085056049973160424035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11551390037366648773616023 17327085056049973160424035)
      ·
        refine ⟨25990627584074959740636053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17327085056049973160424035 25990627584074959740636053)
        ·
          refine ⟨1218310668003513737842315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25990627584074959740636053 1218310668003513737842315)
          ·
            refine ⟨1827466002005270606763473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1218310668003513737842315 1827466002005270606763473)
            ·
              refine ⟨1370599501503952955072605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1827466002005270606763473 1370599501503952955072605)
              ·
                refine ⟨513974813063982358152227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1370599501503952955072605 513974813063982358152227)
                ·
                  refine ⟨770962219595973537228341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 513974813063982358152227 770962219595973537228341)
                  ·
                    refine ⟨72277708087122519115157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 770962219595973537228341 72277708087122519115157)
                    ·
                      rfl

theorem cell23_422281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 5].length) (baseStart_422281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422281 prefixEnd_422281 := by exact prefixLift 422281
  have htrace : WordTrace (prefixWord ++ tailWord_422281) baseStart_422281 baseEnd_422281 := by
    simpa [prefixWord, tailWord_422281, baseEnd_422281] using wordTrace_append hprefix tailTrace_422281
  have hstable : (prefixWord ++ tailWord_422281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422281).length < 2 ^ (prefixWord ++ tailWord_422281).sum := by decide
  have hdescent : baseEnd_422281 < baseStart_422281 := by decide
  rcases family_descends (prefixWord ++ tailWord_422281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422368 : List Nat := [2, 1, 1, 3, 1, 1, 3, 5, 2, 1, 3]
def baseStart_422368 : Nat := 118140960795 + 422368 * 2 ^ 59
def prefixEnd_422368 : Nat := 4983230072969 + 3 ^ 40 * 422368 * 2
def baseEnd_422368 : Nat := 216877797078308716957571

theorem tailTrace_422368 : CollatzResearch.WordTrace tailWord_422368 prefixEnd_422368 216877797078308716957571 := by
  unfold tailWord_422368
  simp only [CollatzResearch.WordTrace]
  refine ⟨7702513266920172778285879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10270017689226897037714505 7702513266920172778285879)
  ·
    refine ⟨11553769900380259167428819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7702513266920172778285879 11553769900380259167428819)
    ·
      refine ⟨17330654850570388751143229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11553769900380259167428819 17330654850570388751143229)
      ·
        refine ⟨6498995568963895781678711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17330654850570388751143229 6498995568963895781678711)
        ·
          refine ⟨9748493353445843672518067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6498995568963895781678711 9748493353445843672518067)
          ·
            refine ⟨14622740030168765508777101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9748493353445843672518067 14622740030168765508777101)
            ·
              refine ⟨5483527511313287065791413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14622740030168765508777101 5483527511313287065791413)
              ·
                refine ⟨514080704185620662417945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5483527511313287065791413 514080704185620662417945)
                ·
                  refine ⟨385560528139215496813459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 514080704185620662417945 385560528139215496813459)
                  ·
                    refine ⟨578340792208823245220189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 385560528139215496813459 578340792208823245220189)
                    ·
                      refine ⟨216877797078308716957571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 578340792208823245220189 216877797078308716957571)
                      ·
                        rfl

theorem cell23_422368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 2, 1, 3].length) (baseStart_422368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422368 prefixEnd_422368 := by exact prefixLift 422368
  have htrace : WordTrace (prefixWord ++ tailWord_422368) baseStart_422368 baseEnd_422368 := by
    simpa [prefixWord, tailWord_422368, baseEnd_422368] using wordTrace_append hprefix tailTrace_422368
  have hstable : (prefixWord ++ tailWord_422368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422368).length < 2 ^ (prefixWord ++ tailWord_422368).sum := by decide
  have hdescent : baseEnd_422368 < baseStart_422368 := by decide
  rcases family_descends (prefixWord ++ tailWord_422368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422384 : List Nat := [2, 1, 1, 1, 3, 3, 1, 2, 1, 8]
def baseStart_422384 : Nat := 118140960795 + 422384 * 2 ^ 59
def prefixEnd_422384 : Nat := 4983230072969 + 3 ^ 40 * 422384 * 2
def baseEnd_422384 : Nat := 72295337589593551452499

theorem tailTrace_422384 : CollatzResearch.WordTrace tailWord_422384 prefixEnd_422384 72295337589593551452499 := by
  unfold tailWord_422384
  simp only [CollatzResearch.WordTrace]
  refine ⟨7702805050891190144577103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10270406734521586859436137 7702805050891190144577103)
  ·
    refine ⟨11554207576336785216865655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7702805050891190144577103 11554207576336785216865655)
    ·
      refine ⟨17331311364505177825298483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11554207576336785216865655 17331311364505177825298483)
      ·
        refine ⟨25996967046757766737947725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17331311364505177825298483 25996967046757766737947725)
        ·
          refine ⟨9748862642534162526730397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25996967046757766737947725 9748862642534162526730397)
          ·
            refine ⟨3655823490950310947523899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9748862642534162526730397 3655823490950310947523899)
            ·
              refine ⟨5483735236425466421285849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3655823490950310947523899 5483735236425466421285849)
              ·
                refine ⟨4112801427319099815964387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5483735236425466421285849 4112801427319099815964387)
                ·
                  refine ⟨6169202140978649723946581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4112801427319099815964387 6169202140978649723946581)
                  ·
                    refine ⟨72295337589593551452499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 6169202140978649723946581 72295337589593551452499)
                    ·
                      rfl

theorem cell23_422384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 1, 8].length) (baseStart_422384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422384 prefixEnd_422384 := by exact prefixLift 422384
  have htrace : WordTrace (prefixWord ++ tailWord_422384) baseStart_422384 baseEnd_422384 := by
    simpa [prefixWord, tailWord_422384, baseEnd_422384] using wordTrace_append hprefix tailTrace_422384
  have hstable : (prefixWord ++ tailWord_422384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422384).length < 2 ^ (prefixWord ++ tailWord_422384).sum := by decide
  have hdescent : baseEnd_422384 < baseStart_422384 := by decide
  rcases family_descends (prefixWord ++ tailWord_422384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422389 : List Nat := [1, 3, 5, 1, 2, 2, 2, 1, 1, 2, 3]
def baseStart_422389 : Nat := 118140960795 + 422389 * 2 ^ 59
def prefixEnd_422389 : Nat := 4983230072969 + 3 ^ 40 * 422389 * 2
def baseEnd_422389 : Nat := 216888580172053134794975

theorem tailTrace_422389 : CollatzResearch.WordTrace tailWord_422389 prefixEnd_422389 216888580172053134794975 := by
  unfold tailWord_422389
  simp only [CollatzResearch.WordTrace]
  refine ⟨15405792466764266143086221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10270528311176177428724147 15405792466764266143086221)
  ·
    refine ⟨5777172175036599803657333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15405792466764266143086221 5777172175036599803657333)
    ·
      refine ⟨541609891409681231592875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5777172175036599803657333 541609891409681231592875)
      ·
        refine ⟨812414837114521847389313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541609891409681231592875 812414837114521847389313)
        ·
          refine ⟨609311127835891385541985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 812414837114521847389313 609311127835891385541985)
          ·
            refine ⟨456983345876918539156489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 609311127835891385541985 456983345876918539156489)
            ·
              refine ⟨342737509407688904367367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 456983345876918539156489 342737509407688904367367)
              ·
                refine ⟨514106264111533356551051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 342737509407688904367367 514106264111533356551051)
                ·
                  refine ⟨771159396167300034826577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 514106264111533356551051 771159396167300034826577)
                  ·
                    refine ⟨578369547125475026119933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 771159396167300034826577 578369547125475026119933)
                    ·
                      refine ⟨216888580172053134794975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 578369547125475026119933 216888580172053134794975)
                      ·
                        rfl

theorem cell23_422389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_422389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422389 prefixEnd_422389 := by exact prefixLift 422389
  have htrace : WordTrace (prefixWord ++ tailWord_422389) baseStart_422389 baseEnd_422389 := by
    simpa [prefixWord, tailWord_422389, baseEnd_422389] using wordTrace_append hprefix tailTrace_422389
  have hstable : (prefixWord ++ tailWord_422389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422389).length < 2 ^ (prefixWord ++ tailWord_422389).sum := by decide
  have hdescent : baseEnd_422389 < baseStart_422389 := by decide
  rcases family_descends (prefixWord ++ tailWord_422389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_422391 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 2, 8, 2]
def baseStart_422391 : Nat := 118140960795 + 422391 * 2 ^ 59
def prefixEnd_422391 : Nat := 4983230072969 + 3 ^ 40 * 422391 * 2
def baseEnd_422391 : Nat := 216889607133362126969965

theorem tailTrace_422391 : CollatzResearch.WordTrace tailWord_422391 prefixEnd_422391 216889607133362126969965 := by
  unfold tailWord_422391
  simp only [CollatzResearch.WordTrace]
  refine ⟨15405865412757020484659027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10270576941838013656439351 15405865412757020484659027)
  ·
    refine ⟨23108798119135530726988541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15405865412757020484659027 23108798119135530726988541)
    ·
      refine ⟨8665799294675824022620703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23108798119135530726988541 8665799294675824022620703)
      ·
        refine ⟨12998698942013736033931055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8665799294675824022620703 12998698942013736033931055)
        ·
          refine ⟨19498048413020604050896583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12998698942013736033931055 19498048413020604050896583)
          ·
            refine ⟨29247072619530906076344875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19498048413020604050896583 29247072619530906076344875)
            ·
              refine ⟨43870608929296359114517313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29247072619530906076344875 43870608929296359114517313)
              ·
                refine ⟨32902956696972269335887985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43870608929296359114517313 32902956696972269335887985)
                ·
                  refine ⟨24677217522729202001915989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32902956696972269335887985 24677217522729202001915989)
                  ·
                    refine ⟨289186142844482835959953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24677217522729202001915989 289186142844482835959953)
                    ·
                      refine ⟨216889607133362126969965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 289186142844482835959953 216889607133362126969965)
                      ·
                        rfl

theorem cell23_422391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 8, 2].length) (baseStart_422391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_422391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_422391 prefixEnd_422391 := by exact prefixLift 422391
  have htrace : WordTrace (prefixWord ++ tailWord_422391) baseStart_422391 baseEnd_422391 := by
    simpa [prefixWord, tailWord_422391, baseEnd_422391] using wordTrace_append hprefix tailTrace_422391
  have hstable : (prefixWord ++ tailWord_422391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_422391).length < 2 ^ (prefixWord ++ tailWord_422391).sum := by decide
  have hdescent : baseEnd_422391 < baseStart_422391 := by decide
  rcases family_descends (prefixWord ++ tailWord_422391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
