import V185TrunkScan23Chunk0741

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4387479 : List Nat := [1, 1, 3, 3, 2, 1, 12]
def baseStart_4387479 : Nat := 118140960795 + 4387479 * 2 ^ 59
def prefixEnd_4387479 : Nat := 4983230072969 + 3 ^ 40 * 4387479 * 2
def baseEnd_4387479 : Nat := 27813402327258576567097

theorem tailTrace_4387479 : CollatzResearch.WordTrace tailWord_4387479 prefixEnd_4387479 27813402327258576567097 := by
  unfold tailWord_4387479
  simp only [CollatzResearch.WordTrace]
  refine ⟨160024505671920379601757491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106683003781280253067838327 160024505671920379601757491)
  ·
    refine ⟨240036758507880569402636237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160024505671920379601757491 240036758507880569402636237)
    ·
      refine ⟨90013784440455213525988589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 240036758507880569402636237 90013784440455213525988589)
      ·
        refine ⟨33755169165170705072245721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90013784440455213525988589 33755169165170705072245721)
        ·
          refine ⟨25316376873878028804184291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33755169165170705072245721 25316376873878028804184291)
          ·
            refine ⟨37974565310817043206276437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25316376873878028804184291 37974565310817043206276437)
            ·
              refine ⟨27813402327258576567097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 37974565310817043206276437 27813402327258576567097)
              ·
                rfl

theorem cell23_4387479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 12].length) (baseStart_4387479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387479 prefixEnd_4387479 := by exact prefixLift 4387479
  have htrace : WordTrace (prefixWord ++ tailWord_4387479) baseStart_4387479 baseEnd_4387479 := by
    simpa [prefixWord, tailWord_4387479, baseEnd_4387479] using wordTrace_append hprefix tailTrace_4387479
  have hstable : (prefixWord ++ tailWord_4387479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387479).length < 2 ^ (prefixWord ++ tailWord_4387479).sum := by decide
  have hdescent : baseEnd_4387479 < baseStart_4387479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387503 : List Nat := [1, 1, 2, 1, 2, 7, 1, 1, 1, 2, 4]
def baseStart_4387503 : Nat := 118140960795 + 4387503 * 2 ^ 59
def prefixEnd_4387503 : Nat := 4983230072969 + 3 ^ 40 * 4387503 * 2
def baseEnd_4387503 : Nat := 2252897912043652608034747

theorem tailTrace_4387503 : CollatzResearch.WordTrace tailWord_4387503 prefixEnd_4387503 2252897912043652608034747 := by
  unfold tailWord_4387503
  simp only [CollatzResearch.WordTrace]
  refine ⟨160025381023833431700631163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106683587349222287800420775 160025381023833431700631163)
  ·
    refine ⟨240038071535750147550946745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160025381023833431700631163 240038071535750147550946745)
    ·
      refine ⟨180028553651812610663210059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240038071535750147550946745 180028553651812610663210059)
      ·
        refine ⟨270042830477718915994815089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180028553651812610663210059 270042830477718915994815089)
        ·
          refine ⟨202532122858289186996111317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 270042830477718915994815089 202532122858289186996111317)
          ·
            refine ⟨4746846629491152820221359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 202532122858289186996111317 4746846629491152820221359)
            ·
              refine ⟨7120269944236729230332039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4746846629491152820221359 7120269944236729230332039)
              ·
                refine ⟨10680404916355093845498059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7120269944236729230332039 10680404916355093845498059)
                ·
                  refine ⟨16020607374532640768247089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10680404916355093845498059 16020607374532640768247089)
                  ·
                    refine ⟨12015455530899480576185317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16020607374532640768247089 12015455530899480576185317)
                    ·
                      refine ⟨2252897912043652608034747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12015455530899480576185317 2252897912043652608034747)
                      ·
                        rfl

theorem cell23_4387503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 2, 4].length) (baseStart_4387503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387503 prefixEnd_4387503 := by exact prefixLift 4387503
  have htrace : WordTrace (prefixWord ++ tailWord_4387503) baseStart_4387503 baseEnd_4387503 := by
    simpa [prefixWord, tailWord_4387503, baseEnd_4387503] using wordTrace_append hprefix tailTrace_4387503
  have hstable : (prefixWord ++ tailWord_4387503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387503).length < 2 ^ (prefixWord ++ tailWord_4387503).sum := by decide
  have hdescent : baseEnd_4387503 < baseStart_4387503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387524 : List Nat := [2, 3, 3, 1, 1, 2, 3, 3, 1, 2, 2]
def baseStart_4387524 : Nat := 118140960795 + 4387524 * 2 ^ 59
def prefixEnd_4387524 : Nat := 4983230072969 + 3 ^ 40 * 4387524 * 2
def baseEnd_4387524 : Nat := 2252908695137397025872151

theorem tailTrace_4387524 : CollatzResearch.WordTrace tailWord_4387524 prefixEnd_4387524 2252908695137397025872151 := by
  unfold tailWord_4387524
  simp only [CollatzResearch.WordTrace]
  refine ⟨80013073478378676143572813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106684097971171568191430417 80013073478378676143572813)
  ·
    refine ⟨30004902554392003553839805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80013073478378676143572813 30004902554392003553839805)
    ·
      refine ⟨11251838457897001332689927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30004902554392003553839805 11251838457897001332689927)
      ·
        refine ⟨16877757686845501999034891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11251838457897001332689927 16877757686845501999034891)
        ·
          refine ⟨25316636530268252998552337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16877757686845501999034891 25316636530268252998552337)
          ·
            refine ⟨18987477397701189748914253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25316636530268252998552337 18987477397701189748914253)
            ·
              refine ⟨7120304024137946155842845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18987477397701189748914253 7120304024137946155842845)
              ·
                refine ⟨2670114009051729808441067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7120304024137946155842845 2670114009051729808441067)
                ·
                  refine ⟨4005171013577594712661601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2670114009051729808441067 4005171013577594712661601)
                  ·
                    refine ⟨3003878260183196034496201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4005171013577594712661601 3003878260183196034496201)
                    ·
                      refine ⟨2252908695137397025872151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3003878260183196034496201 2252908695137397025872151)
                      ·
                        rfl

theorem cell23_4387524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_4387524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387524 prefixEnd_4387524 := by exact prefixLift 4387524
  have htrace : WordTrace (prefixWord ++ tailWord_4387524) baseStart_4387524 baseEnd_4387524 := by
    simpa [prefixWord, tailWord_4387524, baseEnd_4387524] using wordTrace_append hprefix tailTrace_4387524
  have hstable : (prefixWord ++ tailWord_4387524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387524).length < 2 ^ (prefixWord ++ tailWord_4387524).sum := by decide
  have hdescent : baseEnd_4387524 < baseStart_4387524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387529 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 3, 2, 8]
def baseStart_4387529 : Nat := 118140960795 + 4387529 * 2 ^ 59
def prefixEnd_4387529 : Nat := 4983230072969 + 3 ^ 40 * 4387529 * 2
def baseEnd_4387529 : Nat := 2252911262540669506309627

theorem tailTrace_4387529 : CollatzResearch.WordTrace tailWord_4387529 prefixEnd_4387529 2252911262540669506309627 := by
  unfold tailWord_4387529
  simp only [CollatzResearch.WordTrace]
  refine ⟨160026329321739238141077641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106684219547826158760718427 160026329321739238141077641)
  ·
    refine ⟨120019746991304428605808231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160026329321739238141077641 120019746991304428605808231)
    ·
      refine ⟨180029620486956642908712347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120019746991304428605808231 180029620486956642908712347)
      ·
        refine ⟨270044430730434964363068521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180029620486956642908712347 270044430730434964363068521)
        ·
          refine ⟨202533323047826223272301391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 270044430730434964363068521 202533323047826223272301391)
          ·
            refine ⟨303799984571739334908452087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202533323047826223272301391 303799984571739334908452087)
            ·
              refine ⟨455699976857609002362678131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 303799984571739334908452087 455699976857609002362678131)
              ·
                refine ⟨683549965286413503544017197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 455699976857609002362678131 683549965286413503544017197)
                ·
                  refine ⟨256331236982405063829006449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 683549965286413503544017197 256331236982405063829006449)
                  ·
                    refine ⟨192248427736803797871754837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 256331236982405063829006449 192248427736803797871754837)
                    ·
                      refine ⟨2252911262540669506309627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 192248427736803797871754837 2252911262540669506309627)
                      ·
                        rfl

theorem cell23_4387529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 2, 8].length) (baseStart_4387529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387529 prefixEnd_4387529 := by exact prefixLift 4387529
  have htrace : WordTrace (prefixWord ++ tailWord_4387529) baseStart_4387529 baseEnd_4387529 := by
    simpa [prefixWord, tailWord_4387529, baseEnd_4387529] using wordTrace_append hprefix tailTrace_4387529
  have hstable : (prefixWord ++ tailWord_4387529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387529).length < 2 ^ (prefixWord ++ tailWord_4387529).sum := by decide
  have hdescent : baseEnd_4387529 < baseStart_4387529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387541 : List Nat := [1, 3, 2, 5, 2, 1, 1, 1, 3, 2, 2]
def baseStart_4387541 : Nat := 118140960795 + 4387541 * 2 ^ 59
def prefixEnd_4387541 : Nat := 4983230072969 + 3 ^ 40 * 4387541 * 2
def baseEnd_4387541 : Nat := 2252917424308523459359573

theorem tailTrace_4387541 : CollatzResearch.WordTrace tailWord_4387541 prefixEnd_4387541 2252917424308523459359573 := by
  unfold tailWord_4387541
  simp only [CollatzResearch.WordTrace]
  refine ⟨160026766997695764190514477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106684511331797176127009651 160026766997695764190514477)
  ·
    refine ⟨60010037624135911571442929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160026766997695764190514477 60010037624135911571442929)
    ·
      refine ⟨45007528218101933678582197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60010037624135911571442929 45007528218101933678582197)
      ·
        refine ⟨4219455770447056282367081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45007528218101933678582197 4219455770447056282367081)
        ·
          refine ⟨3164591827835292211775311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4219455770447056282367081 3164591827835292211775311)
          ·
            refine ⟨4746887741752938317662967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3164591827835292211775311 4746887741752938317662967)
            ·
              refine ⟨7120331612629407476494451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4746887741752938317662967 7120331612629407476494451)
              ·
                refine ⟨10680497418944111214741677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7120331612629407476494451 10680497418944111214741677)
                ·
                  refine ⟨4005186532104041705528129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10680497418944111214741677 4005186532104041705528129)
                  ·
                    refine ⟨3003889899078031279146097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4005186532104041705528129 3003889899078031279146097)
                    ·
                      refine ⟨2252917424308523459359573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3003889899078031279146097 2252917424308523459359573)
                      ·
                        rfl

theorem cell23_4387541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_4387541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387541 prefixEnd_4387541 := by exact prefixLift 4387541
  have htrace : WordTrace (prefixWord ++ tailWord_4387541) baseStart_4387541 baseEnd_4387541 := by
    simpa [prefixWord, tailWord_4387541, baseEnd_4387541] using wordTrace_append hprefix tailTrace_4387541
  have hstable : (prefixWord ++ tailWord_4387541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387541).length < 2 ^ (prefixWord ++ tailWord_4387541).sum := by decide
  have hdescent : baseEnd_4387541 < baseStart_4387541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387546 : List Nat := [3, 1, 1, 2, 2, 2, 2, 1, 2, 3, 4]
def baseStart_4387546 : Nat := 118140960795 + 4387546 * 2 ^ 59
def prefixEnd_4387546 : Nat := 4983230072969 + 3 ^ 40 * 4387546 * 2
def baseEnd_4387546 : Nat := 2252919991711795939797049

theorem tailTrace_4387546 : CollatzResearch.WordTrace tailWord_4387546 prefixEnd_4387546 2252919991711795939797049 := by
  unfold tailWord_4387546
  simp only [CollatzResearch.WordTrace]
  refine ⟨40006737340669412511111623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106684632908451766696297661 40006737340669412511111623)
  ·
    refine ⟨60010106011004118766667435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40006737340669412511111623 60010106011004118766667435)
    ·
      refine ⟨90015159016506178150001153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60010106011004118766667435 90015159016506178150001153)
      ·
        refine ⟨67511369262379633612500865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90015159016506178150001153 67511369262379633612500865)
        ·
          refine ⟨50633526946784725209375649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67511369262379633612500865 50633526946784725209375649)
          ·
            refine ⟨37975145210088543907031737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50633526946784725209375649 37975145210088543907031737)
            ·
              refine ⟨28481358907566407930273803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37975145210088543907031737 28481358907566407930273803)
              ·
                refine ⟨42722038361349611895410705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28481358907566407930273803 42722038361349611895410705)
                ·
                  refine ⟨32041528771012208921558029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42722038361349611895410705 32041528771012208921558029)
                  ·
                    refine ⟨12015573289129578345584261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32041528771012208921558029 12015573289129578345584261)
                    ·
                      refine ⟨2252919991711795939797049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12015573289129578345584261 2252919991711795939797049)
                      ·
                        rfl

theorem cell23_4387546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_4387546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387546 prefixEnd_4387546 := by exact prefixLift 4387546
  have htrace : WordTrace (prefixWord ++ tailWord_4387546) baseStart_4387546 baseEnd_4387546 := by
    simpa [prefixWord, tailWord_4387546, baseEnd_4387546] using wordTrace_append hprefix tailTrace_4387546
  have hstable : (prefixWord ++ tailWord_4387546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387546).length < 2 ^ (prefixWord ++ tailWord_4387546).sum := by decide
  have hdescent : baseEnd_4387546 < baseStart_4387546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387557 : List Nat := [1, 3, 1, 4, 1, 2, 4, 1, 2, 1, 3]
def baseStart_4387557 : Nat := 118140960795 + 4387557 * 2 ^ 59
def prefixEnd_4387557 : Nat := 4983230072969 + 3 ^ 40 * 4387557 * 2
def baseEnd_4387557 : Nat := 2252925639998995396759499

theorem tailTrace_4387557 : CollatzResearch.WordTrace tailWord_4387557 prefixEnd_4387557 2252925639998995396759499 := by
  unfold tailWord_4387557
  simp only [CollatzResearch.WordTrace]
  refine ⟨160027350565637798923096925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106684900377091865948731283 160027350565637798923096925)
  ·
    refine ⟨60010256462114174596161347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160027350565637798923096925 60010256462114174596161347)
    ·
      refine ⟨90015384693171261894242021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60010256462114174596161347 90015384693171261894242021)
      ·
        refine ⟨16877884629969611605170379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90015384693171261894242021 16877884629969611605170379)
        ·
          refine ⟨25316826944954417407755569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16877884629969611605170379 25316826944954417407755569)
          ·
            refine ⟨18987620208715813055816677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25316826944954417407755569 18987620208715813055816677)
            ·
              refine ⟨3560178789134214947965627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18987620208715813055816677 3560178789134214947965627)
              ·
                refine ⟨5340268183701322421948441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3560178789134214947965627 5340268183701322421948441)
                ·
                  refine ⟨4005201137775991816461331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5340268183701322421948441 4005201137775991816461331)
                  ·
                    refine ⟨6007801706663987724691997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4005201137775991816461331 6007801706663987724691997)
                    ·
                      refine ⟨2252925639998995396759499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6007801706663987724691997 2252925639998995396759499)
                      ·
                        rfl

theorem cell23_4387557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_4387557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387557 prefixEnd_4387557 := by exact prefixLift 4387557
  have htrace : WordTrace (prefixWord ++ tailWord_4387557) baseStart_4387557 baseEnd_4387557 := by
    simpa [prefixWord, tailWord_4387557, baseEnd_4387557] using wordTrace_append hprefix tailTrace_4387557
  have hstable : (prefixWord ++ tailWord_4387557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387557).length < 2 ^ (prefixWord ++ tailWord_4387557).sum := by decide
  have hdescent : baseEnd_4387557 < baseStart_4387557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387563 : List Nat := [1, 1, 1, 1, 2, 4, 1, 5, 1, 4, 2]
def baseStart_4387563 : Nat := 118140960795 + 4387563 * 2 ^ 59
def prefixEnd_4387563 : Nat := 4983230072969 + 3 ^ 40 * 4387563 * 2
def baseEnd_4387563 : Nat := 2252928720882922373284471

theorem tailTrace_4387563 : CollatzResearch.WordTrace tailWord_4387563 prefixEnd_4387563 2252928720882922373284471 := by
  unfold tailWord_4387563
  simp only [CollatzResearch.WordTrace]
  refine ⟨160027569403616061947815343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106685046269077374631876895 160027569403616061947815343)
  ·
    refine ⟨240041354105424092921723015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160027569403616061947815343 240041354105424092921723015)
    ·
      refine ⟨360062031158136139382584523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240041354105424092921723015 360062031158136139382584523)
      ·
        refine ⟨540093046737204209073876785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 360062031158136139382584523 540093046737204209073876785)
        ·
          refine ⟨405069785052903156805407589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 540093046737204209073876785 405069785052903156805407589)
          ·
            refine ⟨75950584697419341901013923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 405069785052903156805407589 75950584697419341901013923)
            ·
              refine ⟨113925877046129012851520885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75950584697419341901013923 113925877046129012851520885)
              ·
                refine ⟨10680550973074594954830083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 113925877046129012851520885 10680550973074594954830083)
                ·
                  refine ⟨16020826459611892432245125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10680550973074594954830083 16020826459611892432245125)
                  ·
                    refine ⟨3003904961177229831045961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16020826459611892432245125 3003904961177229831045961)
                    ·
                      refine ⟨2252928720882922373284471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3003904961177229831045961 2252928720882922373284471)
                      ·
                        rfl

theorem cell23_4387563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 4, 2].length) (baseStart_4387563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387563 prefixEnd_4387563 := by exact prefixLift 4387563
  have htrace : WordTrace (prefixWord ++ tailWord_4387563) baseStart_4387563 baseEnd_4387563 := by
    simpa [prefixWord, tailWord_4387563, baseEnd_4387563] using wordTrace_append hprefix tailTrace_4387563
  have hstable : (prefixWord ++ tailWord_4387563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387563).length < 2 ^ (prefixWord ++ tailWord_4387563).sum := by decide
  have hdescent : baseEnd_4387563 < baseStart_4387563 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387567 : List Nat := [1, 1, 2, 1, 5, 4, 1, 2, 1, 3, 2]
def baseStart_4387567 : Nat := 118140960795 + 4387567 * 2 ^ 59
def prefixEnd_4387567 : Nat := 4983230072969 + 3 ^ 40 * 4387567 * 2
def baseEnd_4387567 : Nat := 2252930774805540357634453

theorem tailTrace_4387567 : CollatzResearch.WordTrace tailWord_4387567 prefixEnd_4387567 2252930774805540357634453 := by
  unfold tailWord_4387567
  simp only [CollatzResearch.WordTrace]
  refine ⟨160027715295601570630960955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106685143530401047087307303 160027715295601570630960955)
  ·
    refine ⟨240041572943402355946441433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160027715295601570630960955 240041572943402355946441433)
    ·
      refine ⟨180031179707551766959831075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240041572943402355946441433 180031179707551766959831075)
      ·
        refine ⟨270046769561327650439746613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180031179707551766959831075 270046769561327650439746613)
        ·
          refine ⟨25316884646374467228726245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 270046769561327650439746613 25316884646374467228726245)
          ·
            refine ⟨4746915871195212605386171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25316884646374467228726245 4746915871195212605386171)
            ·
              refine ⟨7120373806792818908079257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4746915871195212605386171 7120373806792818908079257)
              ·
                refine ⟨5340280355094614181059443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7120373806792818908079257 5340280355094614181059443)
                ·
                  refine ⟨8010420532641921271589165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5340280355094614181059443 8010420532641921271589165)
                  ·
                    refine ⟨3003907699740720476845937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8010420532641921271589165 3003907699740720476845937)
                    ·
                      refine ⟨2252930774805540357634453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3003907699740720476845937 2252930774805540357634453)
                      ·
                        rfl

theorem cell23_4387567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 1, 3, 2].length) (baseStart_4387567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387567 prefixEnd_4387567 := by exact prefixLift 4387567
  have htrace : WordTrace (prefixWord ++ tailWord_4387567) baseStart_4387567 baseEnd_4387567 := by
    simpa [prefixWord, tailWord_4387567, baseEnd_4387567] using wordTrace_append hprefix tailTrace_4387567
  have hstable : (prefixWord ++ tailWord_4387567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387567).length < 2 ^ (prefixWord ++ tailWord_4387567).sum := by decide
  have hdescent : baseEnd_4387567 < baseStart_4387567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387580 : List Nat := [2, 2, 2, 1, 3, 3, 1, 2, 1, 4, 2]
def baseStart_4387580 : Nat := 118140960795 + 4387580 * 2 ^ 59
def prefixEnd_4387580 : Nat := 4983230072969 + 3 ^ 40 * 4387580 * 2
def baseEnd_4387580 : Nat := 2252937450054048806771893

theorem tailTrace_4387580 : CollatzResearch.WordTrace tailWord_4387580 prefixEnd_4387580 2252937450054048806771893 := by
  unfold tailWord_4387580
  simp only [CollatzResearch.WordTrace]
  refine ⟨80014094722277236925592097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106685459629702982567456129 80014094722277236925592097)
  ·
    refine ⟨60010571041707927694194073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80014094722277236925592097 60010571041707927694194073)
    ·
      refine ⟨45007928281280945770645555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60010571041707927694194073 45007928281280945770645555)
      ·
        refine ⟨67511892421921418655968333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45007928281280945770645555 67511892421921418655968333)
        ·
          refine ⟨25316959658220531995988125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67511892421921418655968333 25316959658220531995988125)
          ·
            refine ⟨9493859871832699498495547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25316959658220531995988125 9493859871832699498495547)
            ·
              refine ⟨14240789807749049247743321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9493859871832699498495547 14240789807749049247743321)
              ·
                refine ⟨10680592355811786935807491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14240789807749049247743321 10680592355811786935807491)
                ·
                  refine ⟨16020888533717680403711237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10680592355811786935807491 16020888533717680403711237)
                  ·
                    refine ⟨3003916600072065075695857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16020888533717680403711237 3003916600072065075695857)
                    ·
                      refine ⟨2252937450054048806771893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3003916600072065075695857 2252937450054048806771893)
                      ·
                        rfl

theorem cell23_4387580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 1, 4, 2].length) (baseStart_4387580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387580 prefixEnd_4387580 := by exact prefixLift 4387580
  have htrace : WordTrace (prefixWord ++ tailWord_4387580) baseStart_4387580 baseEnd_4387580 := by
    simpa [prefixWord, tailWord_4387580, baseEnd_4387580] using wordTrace_append hprefix tailTrace_4387580
  have hstable : (prefixWord ++ tailWord_4387580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387580).length < 2 ^ (prefixWord ++ tailWord_4387580).sum := by decide
  have hdescent : baseEnd_4387580 < baseStart_4387580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387603 : List Nat := [1, 1, 1, 2, 1, 3, 5, 4, 5]
def baseStart_4387603 : Nat := 118140960795 + 4387603 * 2 ^ 59
def prefixEnd_4387603 : Nat := 4983230072969 + 3 ^ 40 * 4387603 * 2
def baseEnd_4387603 : Nat := 250327695567678024087143

theorem tailTrace_4387603 : CollatzResearch.WordTrace tailWord_4387603 prefixEnd_4387603 250327695567678024087143 := by
  unfold tailWord_4387603
  simp only [CollatzResearch.WordTrace]
  refine ⟨160029028323471148779271463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106686018882314099186180975 160029028323471148779271463)
  ·
    refine ⟨240043542485206723168907195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160029028323471148779271463 240043542485206723168907195)
    ·
      refine ⟨360065313727810084753360793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240043542485206723168907195 360065313727810084753360793)
      ·
        refine ⟨270048985295857563565020595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 360065313727810084753360793 270048985295857563565020595)
        ·
          refine ⟨405073477943786345347530893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270048985295857563565020595 405073477943786345347530893)
          ·
            refine ⟨151902554228919879505324085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 405073477943786345347530893 151902554228919879505324085)
            ·
              refine ⟨14240864458961238703624133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 151902554228919879505324085 14240864458961238703624133)
              ·
                refine ⟨2670162086055232256929525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14240864458961238703624133 2670162086055232256929525)
                ·
                  refine ⟨250327695567678024087143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2670162086055232256929525 250327695567678024087143)
                  ·
                    rfl

theorem cell23_4387603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 4, 5].length) (baseStart_4387603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387603 prefixEnd_4387603 := by exact prefixLift 4387603
  have htrace : WordTrace (prefixWord ++ tailWord_4387603) baseStart_4387603 baseEnd_4387603 := by
    simpa [prefixWord, tailWord_4387603, baseEnd_4387603] using wordTrace_append hprefix tailTrace_4387603
  have hstable : (prefixWord ++ tailWord_4387603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387603).length < 2 ^ (prefixWord ++ tailWord_4387603).sum := by decide
  have hdescent : baseEnd_4387603 < baseStart_4387603 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387673 : List Nat := [1, 2, 1, 2, 2, 4, 1, 2, 1, 4, 3]
def baseStart_4387673 : Nat := 118140960795 + 4387673 * 2 ^ 59
def prefixEnd_4387673 : Nat := 4983230072969 + 3 ^ 40 * 4387673 * 2
def baseEnd_4387673 : Nat := 2252985203754916942908965

theorem tailTrace_4387673 : CollatzResearch.WordTrace tailWord_4387673 prefixEnd_4387673 2252985203754916942908965 := by
  unfold tailWord_4387673
  simp only [CollatzResearch.WordTrace]
  refine ⟨160031581433217550734319673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106687720955478367156213115 160031581433217550734319673)
  ·
    refine ⟨120023686074913163050739755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160031581433217550734319673 120023686074913163050739755)
    ·
      refine ⟨180035529112369744576109633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120023686074913163050739755 180035529112369744576109633)
      ·
        refine ⟨135026646834277308432082225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180035529112369744576109633 135026646834277308432082225)
        ·
          refine ⟨101269985125707981324061669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135026646834277308432082225 101269985125707981324061669)
          ·
            refine ⟨18988122211070246498261563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101269985125707981324061669 18988122211070246498261563)
            ·
              refine ⟨28482183316605369747392345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18988122211070246498261563 28482183316605369747392345)
              ·
                refine ⟨21361637487454027310544259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28482183316605369747392345 21361637487454027310544259)
                ·
                  refine ⟨32042456231181040965816389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21361637487454027310544259 32042456231181040965816389)
                  ·
                    refine ⟨6007960543346445181090573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32042456231181040965816389 6007960543346445181090573)
                    ·
                      refine ⟨2252985203754916942908965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6007960543346445181090573 2252985203754916942908965)
                      ·
                        rfl

theorem cell23_4387673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 4, 3].length) (baseStart_4387673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387673 prefixEnd_4387673 := by exact prefixLift 4387673
  have htrace : WordTrace (prefixWord ++ tailWord_4387673) baseStart_4387673 baseEnd_4387673 := by
    simpa [prefixWord, tailWord_4387673, baseEnd_4387673] using wordTrace_append hprefix tailTrace_4387673
  have hstable : (prefixWord ++ tailWord_4387673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387673).length < 2 ^ (prefixWord ++ tailWord_4387673).sum := by decide
  have hdescent : baseEnd_4387673 < baseStart_4387673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387697 : List Nat := [1, 2, 2, 2, 1, 4, 3, 3, 1, 4]
def baseStart_4387697 : Nat := 118140960795 + 4387697 * 2 ^ 59
def prefixEnd_4387697 : Nat := 4983230072969 + 3 ^ 40 * 4387697 * 2
def baseEnd_4387697 : Nat := 750999175763541616336285

theorem tailTrace_4387697 : CollatzResearch.WordTrace tailWord_4387697 prefixEnd_4387697 750999175763541616336285 := by
  unfold tailWord_4387697
  simp only [CollatzResearch.WordTrace]
  refine ⟨160032456785130602833193345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106688304523420401888795563 160032456785130602833193345)
  ·
    refine ⟨120024342588847952124895009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160032456785130602833193345 120024342588847952124895009)
    ·
      refine ⟨90018256941635964093671257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120024342588847952124895009 90018256941635964093671257)
      ·
        refine ⟨67513692706226973070253443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90018256941635964093671257 67513692706226973070253443)
        ·
          refine ⟨101270539059340459605380165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67513692706226973070253443 101270539059340459605380165)
          ·
            refine ⟨18988226073626336176008781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101270539059340459605380165 18988226073626336176008781)
            ·
              refine ⟨7120584777609876066003293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18988226073626336176008781 7120584777609876066003293)
              ·
                refine ⟨2670219291603703524751235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7120584777609876066003293 2670219291603703524751235)
                ·
                  refine ⟨4005328937405555287126853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2670219291603703524751235 4005328937405555287126853)
                  ·
                    refine ⟨750999175763541616336285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4005328937405555287126853 750999175763541616336285)
                    ·
                      rfl

theorem cell23_4387697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 3, 1, 4].length) (baseStart_4387697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387697 prefixEnd_4387697 := by exact prefixLift 4387697
  have htrace : WordTrace (prefixWord ++ tailWord_4387697) baseStart_4387697 baseEnd_4387697 := by
    simpa [prefixWord, tailWord_4387697, baseEnd_4387697] using wordTrace_append hprefix tailTrace_4387697
  have hstable : (prefixWord ++ tailWord_4387697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387697).length < 2 ^ (prefixWord ++ tailWord_4387697).sum := by decide
  have hdescent : baseEnd_4387697 < baseStart_4387697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387753 : List Nat := [1, 2, 1, 1, 1, 1, 7, 2, 1, 6]
def baseStart_4387753 : Nat := 118140960795 + 4387753 * 2 ^ 59
def prefixEnd_4387753 : Nat := 4983230072969 + 3 ^ 40 * 4387753 * 2
def baseEnd_4387753 : Nat := 751008760735758876636199

theorem tailTrace_4387753 : CollatzResearch.WordTrace tailWord_4387753 prefixEnd_4387753 751008760735758876636199 := by
  unfold tailWord_4387753
  simp only [CollatzResearch.WordTrace]
  refine ⟨160034499272927724397231913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106689666181951816264821275 160034499272927724397231913)
  ·
    refine ⟨120025874454695793297923935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160034499272927724397231913 120025874454695793297923935)
    ·
      refine ⟨180038811682043689946885903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120025874454695793297923935 180038811682043689946885903)
      ·
        refine ⟨270058217523065534920328855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180038811682043689946885903 270058217523065534920328855)
        ·
          refine ⟨405087326284598302380493283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270058217523065534920328855 405087326284598302380493283)
          ·
            refine ⟨607630989426897453570739925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405087326284598302380493283 607630989426897453570739925)
            ·
              refine ⟨14241351314692909068064217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 607630989426897453570739925 14241351314692909068064217)
              ·
                refine ⟨10681013486019681801048163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14241351314692909068064217 10681013486019681801048163)
                ·
                  refine ⟨16021520229029522701572245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10681013486019681801048163 16021520229029522701572245)
                  ·
                    refine ⟨751008760735758876636199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16021520229029522701572245 751008760735758876636199)
                    ·
                      rfl

theorem cell23_4387753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 6].length) (baseStart_4387753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387753 prefixEnd_4387753 := by exact prefixLift 4387753
  have htrace : WordTrace (prefixWord ++ tailWord_4387753) baseStart_4387753 baseEnd_4387753 := by
    simpa [prefixWord, tailWord_4387753, baseEnd_4387753] using wordTrace_append hprefix tailTrace_4387753
  have hstable : (prefixWord ++ tailWord_4387753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387753).length < 2 ^ (prefixWord ++ tailWord_4387753).sum := by decide
  have hdescent : baseEnd_4387753 < baseStart_4387753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387763 : List Nat := [1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 5]
def baseStart_4387763 : Nat := 118140960795 + 4387763 * 2 ^ 59
def prefixEnd_4387763 : Nat := 4983230072969 + 3 ^ 40 * 4387763 * 2
def baseEnd_4387763 : Nat := 2253031417013821590783551

theorem tailTrace_4387763 : CollatzResearch.WordTrace tailWord_4387763 prefixEnd_4387763 2253031417013821590783551 := by
  unfold tailWord_4387763
  simp only [CollatzResearch.WordTrace]
  refine ⟨160034864002891496105095943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106689909335260997403397295 160034864002891496105095943)
  ·
    refine ⟨240052296004337244157643915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160034864002891496105095943 240052296004337244157643915)
    ·
      refine ⟨360078444006505866236465873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240052296004337244157643915 360078444006505866236465873)
      ·
        refine ⟨270058833004879399677349405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 360078444006505866236465873 270058833004879399677349405)
        ·
          refine ⟨101272062376829774879006027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 270058833004879399677349405 101272062376829774879006027)
          ·
            refine ⟨151908093565244662318509041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101272062376829774879006027 151908093565244662318509041)
            ·
              refine ⟨113931070173933496738881781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151908093565244662318509041 113931070173933496738881781)
              ·
                refine ⟨10681037828806265319270167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 113931070173933496738881781 10681037828806265319270167)
                ·
                  refine ⟨16021556743209397978905251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10681037828806265319270167 16021556743209397978905251)
                  ·
                    refine ⟨24032335114814096968357877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16021556743209397978905251 24032335114814096968357877)
                    ·
                      refine ⟨2253031417013821590783551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24032335114814096968357877 2253031417013821590783551)
                      ·
                        rfl

theorem cell23_4387763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 5].length) (baseStart_4387763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387763 prefixEnd_4387763 := by exact prefixLift 4387763
  have htrace : WordTrace (prefixWord ++ tailWord_4387763) baseStart_4387763 baseEnd_4387763 := by
    simpa [prefixWord, tailWord_4387763, baseEnd_4387763] using wordTrace_append hprefix tailTrace_4387763
  have hstable : (prefixWord ++ tailWord_4387763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387763).length < 2 ^ (prefixWord ++ tailWord_4387763).sum := by decide
  have hdescent : baseEnd_4387763 < baseStart_4387763 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387783 : List Nat := [1, 1, 4, 1, 1, 2, 5, 8]
def baseStart_4387783 : Nat := 118140960795 + 4387783 * 2 ^ 59
def prefixEnd_4387783 : Nat := 4983230072969 + 3 ^ 40 * 4387783 * 2
def baseEnd_4387783 : Nat := 83445988393589315279017

theorem tailTrace_4387783 : CollatzResearch.WordTrace tailWord_4387783 prefixEnd_4387783 83445988393589315279017 := by
  unfold tailWord_4387783
  simp only [CollatzResearch.WordTrace]
  refine ⟨160035593462819039520824003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106690395641879359680549335 160035593462819039520824003)
  ·
    refine ⟨240053390194228559281236005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160035593462819039520824003 240053390194228559281236005)
    ·
      refine ⟨45010010661417854865231751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 240053390194228559281236005 45010010661417854865231751)
      ·
        refine ⟨67515015992126782297847627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45010010661417854865231751 67515015992126782297847627)
        ·
          refine ⟨101272523988190173446771441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67515015992126782297847627 101272523988190173446771441)
          ·
            refine ⟨75954392991142630085078581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101272523988190173446771441 75954392991142630085078581)
            ·
              refine ⟨7120724342919621570476117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75954392991142630085078581 7120724342919621570476117)
              ·
                refine ⟨83445988393589315279017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7120724342919621570476117 83445988393589315279017)
                ·
                  rfl

theorem cell23_4387783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 8].length) (baseStart_4387783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387783 prefixEnd_4387783 := by exact prefixLift 4387783
  have htrace : WordTrace (prefixWord ++ tailWord_4387783) baseStart_4387783 baseEnd_4387783 := by
    simpa [prefixWord, tailWord_4387783, baseEnd_4387783] using wordTrace_append hprefix tailTrace_4387783
  have hstable : (prefixWord ++ tailWord_4387783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387783).length < 2 ^ (prefixWord ++ tailWord_4387783).sum := by decide
  have hdescent : baseEnd_4387783 < baseStart_4387783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387790 : List Nat := [4, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4]
def baseStart_4387790 : Nat := 118140960795 + 4387790 * 2 ^ 59
def prefixEnd_4387790 : Nat := 4983230072969 + 3 ^ 40 * 4387790 * 2
def baseEnd_4387790 : Nat := 2253045280991492985145927

theorem tailTrace_4387790 : CollatzResearch.WordTrace tailWord_4387790 prefixEnd_4387790 2253045280991492985145927 := by
  unfold tailWord_4387790
  simp only [CollatzResearch.WordTrace]
  refine ⟨20004481096724209964541103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106690565849195786477552549 20004481096724209964541103)
  ·
    refine ⟨30006721645086314946811655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20004481096724209964541103 30006721645086314946811655)
    ·
      refine ⟨45010082467629472420217483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30006721645086314946811655 45010082467629472420217483)
      ·
        refine ⟨67515123701444208630326225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45010082467629472420217483 67515123701444208630326225)
        ·
          refine ⟨50636342776083156472744669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67515123701444208630326225 50636342776083156472744669)
          ·
            refine ⟨18988628541031183677279251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50636342776083156472744669 18988628541031183677279251)
            ·
              refine ⟨28482942811546775515918877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18988628541031183677279251 28482942811546775515918877)
              ·
                refine ⟨10681103554330040818469579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28482942811546775515918877 10681103554330040818469579)
                ·
                  refine ⟨16021655331495061227704369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10681103554330040818469579 16021655331495061227704369)
                  ·
                    refine ⟨12016241498621295920778277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16021655331495061227704369 12016241498621295920778277)
                    ·
                      refine ⟨2253045280991492985145927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12016241498621295920778277 2253045280991492985145927)
                      ·
                        rfl

theorem cell23_4387790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_4387790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387790 prefixEnd_4387790 := by exact prefixLift 4387790
  have htrace : WordTrace (prefixWord ++ tailWord_4387790) baseStart_4387790 baseEnd_4387790 := by
    simpa [prefixWord, tailWord_4387790, baseEnd_4387790] using wordTrace_append hprefix tailTrace_4387790
  have hstable : (prefixWord ++ tailWord_4387790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387790).length < 2 ^ (prefixWord ++ tailWord_4387790).sum := by decide
  have hdescent : baseEnd_4387790 < baseStart_4387790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387794 : List Nat := [3, 2, 2, 3, 1, 1, 1, 1, 5, 2, 2]
def baseStart_4387794 : Nat := 118140960795 + 4387794 * 2 ^ 59
def prefixEnd_4387794 : Nat := 4983230072969 + 3 ^ 40 * 4387794 * 2
def baseEnd_4387794 : Nat := 2253047334914110969495909

theorem tailTrace_4387794 : CollatzResearch.WordTrace tailWord_4387794 prefixEnd_4387794 2253047334914110969495909 := by
  unfold tailWord_4387794
  simp only [CollatzResearch.WordTrace]
  refine ⟨40008998666444797099868609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106690663110519458932982957 40008998666444797099868609)
  ·
    refine ⟨30006748999833597824901457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40008998666444797099868609 30006748999833597824901457)
    ·
      refine ⟨22505061749875198368676093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30006748999833597824901457 22505061749875198368676093)
      ·
        refine ⟨8439398156203199388253535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22505061749875198368676093 8439398156203199388253535)
        ·
          refine ⟨12659097234304799082380303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8439398156203199388253535 12659097234304799082380303)
          ·
            refine ⟨18988645851457198623570455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12659097234304799082380303 18988645851457198623570455)
            ·
              refine ⟨28482968777185797935355683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18988645851457198623570455 28482968777185797935355683)
              ·
                refine ⟨42724453165778696903033525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28482968777185797935355683 42724453165778696903033525)
                ·
                  refine ⟨4005417484291752834659393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42724453165778696903033525 4005417484291752834659393)
                  ·
                    refine ⟨3004063113218814625994545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4005417484291752834659393 3004063113218814625994545)
                    ·
                      refine ⟨2253047334914110969495909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3004063113218814625994545 2253047334914110969495909)
                      ·
                        rfl

theorem cell23_4387794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_4387794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387794 prefixEnd_4387794 := by exact prefixLift 4387794
  have htrace : WordTrace (prefixWord ++ tailWord_4387794) baseStart_4387794 baseEnd_4387794 := by
    simpa [prefixWord, tailWord_4387794, baseEnd_4387794] using wordTrace_append hprefix tailTrace_4387794
  have hstable : (prefixWord ++ tailWord_4387794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387794).length < 2 ^ (prefixWord ++ tailWord_4387794).sum := by decide
  have hdescent : baseEnd_4387794 < baseStart_4387794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387800 : List Nat := [2, 1, 2, 2, 2, 4, 3, 7]
def baseStart_4387800 : Nat := 118140960795 + 4387800 * 2 ^ 59
def prefixEnd_4387800 : Nat := 4983230072969 + 3 ^ 40 * 4387800 * 2
def baseEnd_4387800 : Nat := 83446311696223627630403

theorem tailTrace_4387800 : CollatzResearch.WordTrace tailWord_4387800 prefixEnd_4387800 83446311696223627630403 := by
  unfold tailWord_4387800
  simp only [CollatzResearch.WordTrace]
  refine ⟨80018106751878725712096427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106690809002504967616128569 80018106751878725712096427)
  ·
    refine ⟨120027160127818088568144641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80018106751878725712096427 120027160127818088568144641)
    ·
      refine ⟨90020370095863566426108481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120027160127818088568144641 90020370095863566426108481)
      ·
        refine ⟨67515277571897674819581361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90020370095863566426108481 67515277571897674819581361)
        ·
          refine ⟨50636458178923256114686021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67515277571897674819581361 50636458178923256114686021)
          ·
            refine ⟨9494335908548110521503629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50636458178923256114686021 9494335908548110521503629)
            ·
              refine ⟨3560375965705541445563861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9494335908548110521503629 3560375965705541445563861)
              ·
                refine ⟨83446311696223627630403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3560375965705541445563861 83446311696223627630403)
                ·
                  rfl

theorem cell23_4387800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 7].length) (baseStart_4387800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387800 prefixEnd_4387800 := by exact prefixLift 4387800
  have htrace : WordTrace (prefixWord ++ tailWord_4387800) baseStart_4387800 baseEnd_4387800 := by
    simpa [prefixWord, tailWord_4387800, baseEnd_4387800] using wordTrace_append hprefix tailTrace_4387800
  have hstable : (prefixWord ++ tailWord_4387800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387800).length < 2 ^ (prefixWord ++ tailWord_4387800).sum := by decide
  have hdescent : baseEnd_4387800 < baseStart_4387800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387811 : List Nat := [1, 1, 1, 6, 1, 1, 4, 3, 1, 2, 2]
def baseStart_4387811 : Nat := 118140960795 + 4387811 * 2 ^ 59
def prefixEnd_4387811 : Nat := 4983230072969 + 3 ^ 40 * 4387811 * 2
def baseEnd_4387811 : Nat := 2253056064085237402983331

theorem tailTrace_4387811 : CollatzResearch.WordTrace tailWord_4387811 prefixEnd_4387811 2253056064085237402983331 := by
  unfold tailWord_4387811
  simp only [CollatzResearch.WordTrace]
  refine ⟨160036614706717600302843287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106691076471145066868562191 160036614706717600302843287)
  ·
    refine ⟨240054922060076400454264931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160036614706717600302843287 240054922060076400454264931)
    ·
      refine ⟨360082383090114600681397397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240054922060076400454264931 360082383090114600681397397)
      ·
        refine ⟨16878861707349121906940503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 360082383090114600681397397 16878861707349121906940503)
        ·
          refine ⟨25318292561023682860410755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16878861707349121906940503 25318292561023682860410755)
          ·
            refine ⟨37977438841535524290616133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25318292561023682860410755 37977438841535524290616133)
            ·
              refine ⟨7120769782787910804490525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37977438841535524290616133 7120769782787910804490525)
              ·
                refine ⟨2670288668545466551683947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7120769782787910804490525 2670288668545466551683947)
                ·
                  refine ⟨4005433002818199827525921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2670288668545466551683947 4005433002818199827525921)
                  ·
                    refine ⟨3004074752113649870644441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4005433002818199827525921 3004074752113649870644441)
                    ·
                      refine ⟨2253056064085237402983331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3004074752113649870644441 2253056064085237402983331)
                      ·
                        rfl

theorem cell23_4387811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_4387811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387811 prefixEnd_4387811 := by exact prefixLift 4387811
  have htrace : WordTrace (prefixWord ++ tailWord_4387811) baseStart_4387811 baseEnd_4387811 := by
    simpa [prefixWord, tailWord_4387811, baseEnd_4387811] using wordTrace_append hprefix tailTrace_4387811
  have hstable : (prefixWord ++ tailWord_4387811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387811).length < 2 ^ (prefixWord ++ tailWord_4387811).sum := by decide
  have hdescent : baseEnd_4387811 < baseStart_4387811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387854 : List Nat := [4, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2]
def baseStart_4387854 : Nat := 118140960795 + 4387854 * 2 ^ 59
def prefixEnd_4387854 : Nat := 4983230072969 + 3 ^ 40 * 4387854 * 2
def baseEnd_4387854 : Nat := 2253078143753380734745633

theorem tailTrace_4387854 : CollatzResearch.WordTrace tailWord_4387854 prefixEnd_4387854 2253078143753380734745633 := by
  unfold tailWord_4387854
  simp only [CollatzResearch.WordTrace]
  refine ⟨20004772880695227330832327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106692122030374545764439077 20004772880695227330832327)
  ·
    refine ⟨30007159321042840996248491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20004772880695227330832327 30007159321042840996248491)
    ·
      refine ⟨45010738981564261494372737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30007159321042840996248491 45010738981564261494372737)
      ·
        refine ⟨33758054236173196120779553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45010738981564261494372737 33758054236173196120779553)
        ·
          refine ⟨25318540677129897090584665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33758054236173196120779553 25318540677129897090584665)
          ·
            refine ⟨18988905507847422817938499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25318540677129897090584665 18988905507847422817938499)
            ·
              refine ⟨28483358261771134226907749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18988905507847422817938499 28483358261771134226907749)
              ·
                refine ⟨5340629674082087667545203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28483358261771134226907749 5340629674082087667545203)
                ·
                  refine ⟨8010944511123131501317805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5340629674082087667545203 8010944511123131501317805)
                  ·
                    refine ⟨3004104191671174312994177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8010944511123131501317805 3004104191671174312994177)
                    ·
                      refine ⟨2253078143753380734745633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3004104191671174312994177 2253078143753380734745633)
                      ·
                        rfl

theorem cell23_4387854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_4387854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387854 prefixEnd_4387854 := by exact prefixLift 4387854
  have htrace : WordTrace (prefixWord ++ tailWord_4387854) baseStart_4387854 baseEnd_4387854 := by
    simpa [prefixWord, tailWord_4387854, baseEnd_4387854] using wordTrace_append hprefix tailTrace_4387854
  have hstable : (prefixWord ++ tailWord_4387854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387854).length < 2 ^ (prefixWord ++ tailWord_4387854).sum := by decide
  have hdescent : baseEnd_4387854 < baseStart_4387854 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387883 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 7]
def baseStart_4387883 : Nat := 118140960795 + 4387883 * 2 ^ 59
def prefixEnd_4387883 : Nat := 4983230072969 + 3 ^ 40 * 4387883 * 2
def baseEnd_4387883 : Nat := 2253093034692361121282999

theorem tailTrace_4387883 : CollatzResearch.WordTrace tailWord_4387883 prefixEnd_4387883 2253093034692361121282999 := by
  unfold tailWord_4387883
  simp only [CollatzResearch.WordTrace]
  refine ⟨160039240762456756599464303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106692827174971171066309535 160039240762456756599464303)
  ·
    refine ⟨240058861143685134899196455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160039240762456756599464303 240058861143685134899196455)
    ·
      refine ⟨360088291715527702348794683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240058861143685134899196455 360088291715527702348794683)
      ·
        refine ⟨540132437573291553523192025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 360088291715527702348794683 540132437573291553523192025)
        ·
          refine ⟨405099328179968665142394019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 540132437573291553523192025 405099328179968665142394019)
          ·
            refine ⟨607648992269952997713591029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405099328179968665142394019 607648992269952997713591029)
            ·
              refine ⟨56967093025308093535649159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 607648992269952997713591029 56967093025308093535649159)
              ·
                refine ⟨85450639537962140303473739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56967093025308093535649159 85450639537962140303473739)
                ·
                  refine ⟨128175959306943210455210609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85450639537962140303473739 128175959306943210455210609)
                  ·
                    refine ⟨96131969480207407841407957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 128175959306943210455210609 96131969480207407841407957)
                    ·
                      refine ⟨2253093034692361121282999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 96131969480207407841407957 2253093034692361121282999)
                      ·
                        rfl

theorem cell23_4387883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 7].length) (baseStart_4387883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387883 prefixEnd_4387883 := by exact prefixLift 4387883
  have htrace : WordTrace (prefixWord ++ tailWord_4387883) baseStart_4387883 baseEnd_4387883 := by
    simpa [prefixWord, tailWord_4387883, baseEnd_4387883] using wordTrace_append hprefix tailTrace_4387883
  have hstable : (prefixWord ++ tailWord_4387883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387883).length < 2 ^ (prefixWord ++ tailWord_4387883).sum := by decide
  have hdescent : baseEnd_4387883 < baseStart_4387883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387884 : List Nat := [2, 2, 1, 1, 1, 2, 4, 4, 2, 2, 2]
def baseStart_4387884 : Nat := 118140960795 + 4387884 * 2 ^ 59
def prefixEnd_4387884 : Nat := 4983230072969 + 3 ^ 40 * 4387884 * 2
def baseEnd_4387884 : Nat := 2253093548173015617370495

theorem tailTrace_4387884 : CollatzResearch.WordTrace tailWord_4387884 prefixEnd_4387884 2253093548173015617370495 := by
  unfold tailWord_4387884
  simp only [CollatzResearch.WordTrace]
  refine ⟨80019638617726566885125353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106692851490302089180167137 80019638617726566885125353)
  ·
    refine ⟨60014728963294925163844015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80019638617726566885125353 60014728963294925163844015)
    ·
      refine ⟨90022093444942387745766023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60014728963294925163844015 90022093444942387745766023)
      ·
        refine ⟨135033140167413581618649035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90022093444942387745766023 135033140167413581618649035)
        ·
          refine ⟨202549710251120372427973553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135033140167413581618649035 202549710251120372427973553)
          ·
            refine ⟨151912282688340279320980165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202549710251120372427973553 151912282688340279320980165)
            ·
              refine ⟨28483553004063802372683781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 151912282688340279320980165 28483553004063802372683781)
              ·
                refine ⟨5340666188261962944878209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28483553004063802372683781 5340666188261962944878209)
                ·
                  refine ⟨4005499641196472208658657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5340666188261962944878209 4005499641196472208658657)
                  ·
                    refine ⟨3004124730897354156493993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4005499641196472208658657 3004124730897354156493993)
                    ·
                      refine ⟨2253093548173015617370495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3004124730897354156493993 2253093548173015617370495)
                      ·
                        rfl

theorem cell23_4387884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 2, 2].length) (baseStart_4387884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387884 prefixEnd_4387884 := by exact prefixLift 4387884
  have htrace : WordTrace (prefixWord ++ tailWord_4387884) baseStart_4387884 baseEnd_4387884 := by
    simpa [prefixWord, tailWord_4387884, baseEnd_4387884] using wordTrace_append hprefix tailTrace_4387884
  have hstable : (prefixWord ++ tailWord_4387884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387884).length < 2 ^ (prefixWord ++ tailWord_4387884).sum := by decide
  have hdescent : baseEnd_4387884 < baseStart_4387884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387901 : List Nat := [1, 4, 1, 3, 1, 3, 1, 3, 2, 2, 2]
def baseStart_4387901 : Nat := 118140960795 + 4387901 * 2 ^ 59
def prefixEnd_4387901 : Nat := 4983230072969 + 3 ^ 40 * 4387901 * 2
def baseEnd_4387901 : Nat := 2253102277344142050857917

theorem tailTrace_4387901 : CollatzResearch.WordTrace tailWord_4387901 prefixEnd_4387901 2253102277344142050857917 := by
  unfold tailWord_4387901
  simp only [CollatzResearch.WordTrace]
  refine ⟨160039897276391545673619557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106693264850927697115746371 160039897276391545673619557)
  ·
    refine ⟨30007480739323414813803667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160039897276391545673619557 30007480739323414813803667)
    ·
      refine ⟨45011221108985122220705501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30007480739323414813803667 45011221108985122220705501)
      ·
        refine ⟨16879207915869420832764563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45011221108985122220705501 16879207915869420832764563)
        ·
          refine ⟨25318811873804131249146845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16879207915869420832764563 25318811873804131249146845)
          ·
            refine ⟨9494554452676549218430067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25318811873804131249146845 9494554452676549218430067)
            ·
              refine ⟨14241831679014823827645101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9494554452676549218430067 14241831679014823827645101)
              ·
                refine ⟨5340686879630558935366913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14241831679014823827645101 5340686879630558935366913)
                ·
                  refine ⟨4005515159722919201525185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5340686879630558935366913 4005515159722919201525185)
                  ·
                    refine ⟨3004136369792189401143889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4005515159722919201525185 3004136369792189401143889)
                    ·
                      refine ⟨2253102277344142050857917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3004136369792189401143889 2253102277344142050857917)
                      ·
                        rfl

theorem cell23_4387901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_4387901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387901 prefixEnd_4387901 := by exact prefixLift 4387901
  have htrace : WordTrace (prefixWord ++ tailWord_4387901) baseStart_4387901 baseEnd_4387901 := by
    simpa [prefixWord, tailWord_4387901, baseEnd_4387901] using wordTrace_append hprefix tailTrace_4387901
  have hstable : (prefixWord ++ tailWord_4387901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387901).length < 2 ^ (prefixWord ++ tailWord_4387901).sum := by decide
  have hdescent : baseEnd_4387901 < baseStart_4387901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387940 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 3, 3, 4]
def baseStart_4387940 : Nat := 118140960795 + 4387940 * 2 ^ 59
def prefixEnd_4387940 : Nat := 4983230072969 + 3 ^ 40 * 4387940 * 2
def baseEnd_4387940 : Nat := 2253122303089667398270237

theorem tailTrace_4387940 : CollatzResearch.WordTrace tailWord_4387940 prefixEnd_4387940 2253122303089667398270237 := by
  unfold tailWord_4387940
  simp only [CollatzResearch.WordTrace]
  refine ⟨80020659861625127667144637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106694213148833503556192849 80020659861625127667144637)
  ·
    refine ⟨30007747448109422875179239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80020659861625127667144637 30007747448109422875179239)
    ·
      refine ⟨45011621172164134312768859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30007747448109422875179239 45011621172164134312768859)
      ·
        refine ⟨67517431758246201469153289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45011621172164134312768859 67517431758246201469153289)
        ·
          refine ⟨50638073818684651101864967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67517431758246201469153289 50638073818684651101864967)
          ·
            refine ⟨75957110728026976652797451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50638073818684651101864967 75957110728026976652797451)
            ·
              refine ⟨113935666092040464979196177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75957110728026976652797451 113935666092040464979196177)
              ·
                refine ⟨85451749569030348734397133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113935666092040464979196177 85451749569030348734397133)
                ·
                  refine ⟨32044406088386380775398925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85451749569030348734397133 32044406088386380775398925)
                  ·
                    refine ⟨12016652283144892790774597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32044406088386380775398925 12016652283144892790774597)
                    ·
                      refine ⟨2253122303089667398270237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12016652283144892790774597 2253122303089667398270237)
                      ·
                        rfl

theorem cell23_4387940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_4387940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387940 prefixEnd_4387940 := by exact prefixLift 4387940
  have htrace : WordTrace (prefixWord ++ tailWord_4387940) baseStart_4387940 baseEnd_4387940 := by
    simpa [prefixWord, tailWord_4387940, baseEnd_4387940] using wordTrace_append hprefix tailTrace_4387940
  have hstable : (prefixWord ++ tailWord_4387940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387940).length < 2 ^ (prefixWord ++ tailWord_4387940).sum := by decide
  have hdescent : baseEnd_4387940 < baseStart_4387940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387977 : List Nat := [1, 2, 1, 1, 4, 4, 1, 1, 1, 4, 3]
def baseStart_4387977 : Nat := 118140960795 + 4387977 * 2 ^ 59
def prefixEnd_4387977 : Nat := 4983230072969 + 3 ^ 40 * 4387977 * 2
def baseEnd_4387977 : Nat := 2253141301873883753507567

theorem tailTrace_4387977 : CollatzResearch.WordTrace tailWord_4387977 prefixEnd_4387977 2253141301873883753507567 := by
  unfold tailWord_4387977
  simp only [CollatzResearch.WordTrace]
  refine ⟨160042669224116210653386185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106695112816077473768924123 160042669224116210653386185)
  ·
    refine ⟨120032001918087157990039639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160042669224116210653386185 120032001918087157990039639)
    ·
      refine ⟨180048002877130736985059459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120032001918087157990039639 180048002877130736985059459)
      ·
        refine ⟨270072004315696105477589189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180048002877130736985059459 270072004315696105477589189)
        ·
          refine ⟨50638500809193019777047973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 270072004315696105477589189 50638500809193019777047973)
          ·
            refine ⟨9494718901723691208196495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50638500809193019777047973 9494718901723691208196495)
            ·
              refine ⟨14242078352585536812294743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9494718901723691208196495 14242078352585536812294743)
              ·
                refine ⟨21363117528878305218442115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14242078352585536812294743 21363117528878305218442115)
                ·
                  refine ⟨32044676293317457827663173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21363117528878305218442115 32044676293317457827663173)
                  ·
                    refine ⟨6008376804997023342686845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32044676293317457827663173 6008376804997023342686845)
                    ·
                      refine ⟨2253141301873883753507567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6008376804997023342686845 2253141301873883753507567)
                      ·
                        rfl

theorem cell23_4387977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 4, 3].length) (baseStart_4387977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387977 prefixEnd_4387977 := by exact prefixLift 4387977
  have htrace : WordTrace (prefixWord ++ tailWord_4387977) baseStart_4387977 baseEnd_4387977 := by
    simpa [prefixWord, tailWord_4387977, baseEnd_4387977] using wordTrace_append hprefix tailTrace_4387977
  have hstable : (prefixWord ++ tailWord_4387977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387977).length < 2 ^ (prefixWord ++ tailWord_4387977).sum := by decide
  have hdescent : baseEnd_4387977 < baseStart_4387977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388000 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 8]
def baseStart_4388000 : Nat := 118140960795 + 4388000 * 2 ^ 59
def prefixEnd_4388000 : Nat := 4983230072969 + 3 ^ 40 * 4388000 * 2
def baseEnd_4388000 : Nat := 2253153111928937163519961

theorem tailTrace_4388000 : CollatzResearch.WordTrace tailWord_4388000 prefixEnd_4388000 2253153111928937163519961 := by
  unfold tailWord_4388000
  simp only [CollatzResearch.WordTrace]
  refine ⟨80021754051516442790736727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106695672068688590387648969 80021754051516442790736727)
  ·
    refine ⟨120032631077274664186105091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80021754051516442790736727 120032631077274664186105091)
    ·
      refine ⟨180048946615911996279157637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120032631077274664186105091 180048946615911996279157637)
      ·
        refine ⟨33759177490483499302342057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 180048946615911996279157637 33759177490483499302342057)
        ·
          refine ⟨25319383117862624476756543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33759177490483499302342057 25319383117862624476756543)
          ·
            refine ⟨37979074676793936715134815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25319383117862624476756543 37979074676793936715134815)
            ·
              refine ⟨56968612015190905072702223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37979074676793936715134815 56968612015190905072702223)
              ·
                refine ⟨85452918022786357609053335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56968612015190905072702223 85452918022786357609053335)
                ·
                  refine ⟨128179377034179536413580003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85452918022786357609053335 128179377034179536413580003)
                  ·
                    refine ⟨192269065551269304620370005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 128179377034179536413580003 192269065551269304620370005)
                    ·
                      refine ⟨2253153111928937163519961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 192269065551269304620370005 2253153111928937163519961)
                      ·
                        rfl

theorem cell23_4388000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_4388000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4388000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4388000 prefixEnd_4388000 := by exact prefixLift 4388000
  have htrace : WordTrace (prefixWord ++ tailWord_4388000) baseStart_4388000 baseEnd_4388000 := by
    simpa [prefixWord, tailWord_4388000, baseEnd_4388000] using wordTrace_append hprefix tailTrace_4388000
  have hstable : (prefixWord ++ tailWord_4388000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388000).length < 2 ^ (prefixWord ++ tailWord_4388000).sum := by decide
  have hdescent : baseEnd_4388000 < baseStart_4388000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388094 : List Nat := [4, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4]
def baseStart_4388094 : Nat := 118140960795 + 4388094 * 2 ^ 59
def prefixEnd_4388094 : Nat := 4983230072969 + 3 ^ 40 * 4388094 * 2
def baseEnd_4388094 : Nat := 2253201379110459795744529

theorem tailTrace_4388094 : CollatzResearch.WordTrace tailWord_4388094 prefixEnd_4388094 2253201379110459795744529 := by
  unfold tailWord_4388094
  simp only [CollatzResearch.WordTrace]
  refine ⟨20005867070586542454424417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106697957709794893090263557 20005867070586542454424417)
  ·
    refine ⟨15004400302939906840818313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20005867070586542454424417 15004400302939906840818313)
    ·
      refine ⟨11253300227204930130613735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15004400302939906840818313 11253300227204930130613735)
      ·
        refine ⟨16879950340807395195920603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11253300227204930130613735 16879950340807395195920603)
        ·
          refine ⟨25319925511211092793880905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16879950340807395195920603 25319925511211092793880905)
          ·
            refine ⟨18989944133408319595410679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25319925511211092793880905 18989944133408319595410679)
            ·
              refine ⟨28484916200112479393116019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18989944133408319595410679 28484916200112479393116019)
              ·
                refine ⟨42727374300168719089674029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28484916200112479393116019 42727374300168719089674029)
                ·
                  refine ⟨16022765362563269658627761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42727374300168719089674029 16022765362563269658627761)
                  ·
                    refine ⟨12017074021922452243970821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16022765362563269658627761 12017074021922452243970821)
                    ·
                      refine ⟨2253201379110459795744529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12017074021922452243970821 2253201379110459795744529)
                      ·
                        rfl

theorem cell23_4388094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_4388094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4388094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4388094 prefixEnd_4388094 := by exact prefixLift 4388094
  have htrace : WordTrace (prefixWord ++ tailWord_4388094) baseStart_4388094 baseEnd_4388094 := by
    simpa [prefixWord, tailWord_4388094, baseEnd_4388094] using wordTrace_append hprefix tailTrace_4388094
  have hstable : (prefixWord ++ tailWord_4388094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388094).length < 2 ^ (prefixWord ++ tailWord_4388094).sum := by decide
  have hdescent : baseEnd_4388094 < baseStart_4388094 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388101 : List Nat := [1, 3, 1, 1, 2, 1, 7, 1, 1, 2, 3]
def baseStart_4388101 : Nat := 118140960795 + 4388101 * 2 ^ 59
def prefixEnd_4388101 : Nat := 4983230072969 + 3 ^ 40 * 4388101 * 2
def baseEnd_4388101 : Nat := 2253204973475041268356997

theorem tailTrace_4388101 : CollatzResearch.WordTrace tailWord_4388101 prefixEnd_4388101 2253204973475041268356997 := by
  unfold tailWord_4388101
  simp only [CollatzResearch.WordTrace]
  refine ⟨160047191875666979830900157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106698127917111319887266771 160047191875666979830900157)
  ·
    refine ⟨60017696953375117436587559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160047191875666979830900157 60017696953375117436587559)
    ·
      refine ⟨90026545430062676154881339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60017696953375117436587559 90026545430062676154881339)
      ·
        refine ⟨135039818145094014232322009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90026545430062676154881339 135039818145094014232322009)
        ·
          refine ⟨101279863608820510674241507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135039818145094014232322009 101279863608820510674241507)
          ·
            refine ⟨151919795413230766011362261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101279863608820510674241507 151919795413230766011362261)
            ·
              refine ⟨3560620204997596078391303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 151919795413230766011362261 3560620204997596078391303)
              ·
                refine ⟨5340930307496394117586955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3560620204997596078391303 5340930307496394117586955)
                ·
                  refine ⟨8011395461244591176380433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5340930307496394117586955 8011395461244591176380433)
                  ·
                    refine ⟨6008546595933443382285325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8011395461244591176380433 6008546595933443382285325)
                    ·
                      refine ⟨2253204973475041268356997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6008546595933443382285325 2253204973475041268356997)
                      ·
                        rfl

theorem cell23_4388101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 1, 2, 3].length) (baseStart_4388101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4388101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4388101 prefixEnd_4388101 := by exact prefixLift 4388101
  have htrace : WordTrace (prefixWord ++ tailWord_4388101) baseStart_4388101 baseEnd_4388101 := by
    simpa [prefixWord, tailWord_4388101, baseEnd_4388101] using wordTrace_append hprefix tailTrace_4388101
  have hstable : (prefixWord ++ tailWord_4388101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388101).length < 2 ^ (prefixWord ++ tailWord_4388101).sum := by decide
  have hdescent : baseEnd_4388101 < baseStart_4388101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388131 : List Nat := [1, 1, 1, 4, 2, 3, 2, 3, 2, 1, 3]
def baseStart_4388131 : Nat := 118140960795 + 4388131 * 2 ^ 59
def prefixEnd_4388131 : Nat := 4983230072969 + 3 ^ 40 * 4388131 * 2
def baseEnd_4388131 : Nat := 2253220377894676150981859

theorem tailTrace_4388131 : CollatzResearch.WordTrace tailWord_4388131 prefixEnd_4388131 2253220377894676150981859 := by
  unfold tailWord_4388131
  simp only [CollatzResearch.WordTrace]
  refine ⟨160048286065558294954492247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106698857377038863302994831 160048286065558294954492247)
  ·
    refine ⟨240072429098337442431738371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160048286065558294954492247 240072429098337442431738371)
    ·
      refine ⟨360108643647506163647607557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240072429098337442431738371 360108643647506163647607557)
      ·
        refine ⟨67520370683907405683926417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 360108643647506163647607557 67520370683907405683926417)
        ·
          refine ⟨50640278012930554262944813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67520370683907405683926417 50640278012930554262944813)
          ·
            refine ⟨18990104254848957848604305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50640278012930554262944813 18990104254848957848604305)
            ·
              refine ⟨14242578191136718386453229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18990104254848957848604305 14242578191136718386453229)
              ·
                refine ⟨5340966821676269394919961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14242578191136718386453229 5340966821676269394919961)
                ·
                  refine ⟨4005725116257202046189971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5340966821676269394919961 4005725116257202046189971)
                  ·
                    refine ⟨6008587674385803069284957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4005725116257202046189971 6008587674385803069284957)
                    ·
                      refine ⟨2253220377894676150981859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6008587674385803069284957 2253220377894676150981859)
                      ·
                        rfl

theorem cell23_4388131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 3, 2, 1, 3].length) (baseStart_4388131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4388131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4388131 prefixEnd_4388131 := by exact prefixLift 4388131
  have htrace : WordTrace (prefixWord ++ tailWord_4388131) baseStart_4388131 baseEnd_4388131 := by
    simpa [prefixWord, tailWord_4388131, baseEnd_4388131] using wordTrace_append hprefix tailTrace_4388131
  have hstable : (prefixWord ++ tailWord_4388131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388131).length < 2 ^ (prefixWord ++ tailWord_4388131).sum := by decide
  have hdescent : baseEnd_4388131 < baseStart_4388131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388158 : List Nat := [4, 2, 1, 2, 1, 1, 3, 3, 1, 3, 2]
def baseStart_4388158 : Nat := 118140960795 + 4388158 * 2 ^ 59
def prefixEnd_4388158 : Nat := 4983230072969 + 3 ^ 40 * 4388158 * 2
def baseEnd_4388158 : Nat := 2253234241872347545344235

theorem tailTrace_4388158 : CollatzResearch.WordTrace tailWord_4388158 prefixEnd_4388158 2253234241872347545344235 := by
  unfold tailWord_4388158
  simp only [CollatzResearch.WordTrace]
  refine ⟨20006158854557559820715641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106699513890973652377150085 20006158854557559820715641)
  ·
    refine ⟨15004619140918169865536731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20006158854557559820715641 15004619140918169865536731)
    ·
      refine ⟨22506928711377254798305097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15004619140918169865536731 22506928711377254798305097)
      ·
        refine ⟨16880196533532941098728823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22506928711377254798305097 16880196533532941098728823)
        ·
          refine ⟨25320294800299411648093235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16880196533532941098728823 25320294800299411648093235)
          ·
            refine ⟨37980442200449117472139853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25320294800299411648093235 37980442200449117472139853)
            ·
              refine ⟨14242665825168419052052445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37980442200449117472139853 14242665825168419052052445)
              ·
                refine ⟨5340999684438157144519667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14242665825168419052052445 5340999684438157144519667)
                ·
                  refine ⟨8011499526657235716779501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5340999684438157144519667 8011499526657235716779501)
                  ·
                    refine ⟨3004312322496463393792313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8011499526657235716779501 3004312322496463393792313)
                    ·
                      refine ⟨2253234241872347545344235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3004312322496463393792313 2253234241872347545344235)
                      ·
                        rfl

theorem cell23_4388158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_4388158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4388158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4388158 prefixEnd_4388158 := by exact prefixLift 4388158
  have htrace : WordTrace (prefixWord ++ tailWord_4388158) baseStart_4388158 baseEnd_4388158 := by
    simpa [prefixWord, tailWord_4388158, baseEnd_4388158] using wordTrace_append hprefix tailTrace_4388158
  have hstable : (prefixWord ++ tailWord_4388158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388158).length < 2 ^ (prefixWord ++ tailWord_4388158).sum := by decide
  have hdescent : baseEnd_4388158 < baseStart_4388158 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388194 : List Nat := [3, 3, 2, 1, 1, 1, 1, 4, 7]
def baseStart_4388194 : Nat := 118140960795 + 4388194 * 2 ^ 59
def prefixEnd_4388194 : Nat := 4983230072969 + 3 ^ 40 * 4388194 * 2
def baseEnd_4388194 : Nat := 250361414130656600499341

theorem tailTrace_4388194 : CollatzResearch.WordTrace tailWord_4388194 prefixEnd_4388194 250361414130656600499341 := by
  unfold tailWord_4388194
  simp only [CollatzResearch.WordTrace]
  refine ⟨40012645966082514178508909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106700389242886704476023757 40012645966082514178508909)
  ·
    refine ⟨15004742237280942816940841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40012645966082514178508909 15004742237280942816940841)
    ·
      refine ⟨11253556677960707112705631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15004742237280942816940841 11253556677960707112705631)
      ·
        refine ⟨16880335016941060669058447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11253556677960707112705631 16880335016941060669058447)
        ·
          refine ⟨25320502525411591003587671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16880335016941060669058447 25320502525411591003587671)
          ·
            refine ⟨37980753788117386505381507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25320502525411591003587671 37980753788117386505381507)
            ·
              refine ⟨56971130682176079758072261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37980753788117386505381507 56971130682176079758072261)
              ·
                refine ⟨10682087002908014954638549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56971130682176079758072261 10682087002908014954638549)
                ·
                  refine ⟨250361414130656600499341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10682087002908014954638549 250361414130656600499341)
                  ·
                    rfl

theorem cell23_4388194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_4388194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4388194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4388194 prefixEnd_4388194 := by exact prefixLift 4388194
  have htrace : WordTrace (prefixWord ++ tailWord_4388194) baseStart_4388194 baseEnd_4388194 := by
    simpa [prefixWord, tailWord_4388194, baseEnd_4388194] using wordTrace_append hprefix tailTrace_4388194
  have hstable : (prefixWord ++ tailWord_4388194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388194).length < 2 ^ (prefixWord ++ tailWord_4388194).sum := by decide
  have hdescent : baseEnd_4388194 < baseStart_4388194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388207 : List Nat := [1, 1, 2, 1, 3, 1, 3, 3, 1, 7]
def baseStart_4388207 : Nat := 118140960795 + 4388207 * 2 ^ 59
def prefixEnd_4388207 : Nat := 4983230072969 + 3 ^ 40 * 4388207 * 2
def baseEnd_4388207 : Nat := 751086467474805951210503

theorem tailTrace_4388207 : CollatzResearch.WordTrace tailWord_4388207 prefixEnd_4388207 751086467474805951210503 := by
  unfold tailWord_4388207
  simp only [CollatzResearch.WordTrace]
  refine ⟨160051058013282959934258875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106700705342188639956172583 160051058013282959934258875)
  ·
    refine ⟨240076587019924439901388313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160051058013282959934258875 240076587019924439901388313)
    ·
      refine ⟨180057440264943329926041235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240076587019924439901388313 180057440264943329926041235)
      ·
        refine ⟨270086160397414994889061853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180057440264943329926041235 270086160397414994889061853)
        ·
          refine ⟨101282310149030623083398195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 270086160397414994889061853 101282310149030623083398195)
          ·
            refine ⟨151923465223545934625097293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101282310149030623083398195 151923465223545934625097293)
            ·
              refine ⟨56971299458829725484411485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 151923465223545934625097293 56971299458829725484411485)
              ·
                refine ⟨21364237297061147056654307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56971299458829725484411485 21364237297061147056654307)
                ·
                  refine ⟨32046355945591720584981461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21364237297061147056654307 32046355945591720584981461)
                  ·
                    refine ⟨751086467474805951210503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32046355945591720584981461 751086467474805951210503)
                    ·
                      rfl

theorem cell23_4388207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 7].length) (baseStart_4388207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4388207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4388207 prefixEnd_4388207 := by exact prefixLift 4388207
  have htrace : WordTrace (prefixWord ++ tailWord_4388207) baseStart_4388207 baseEnd_4388207 := by
    simpa [prefixWord, tailWord_4388207, baseEnd_4388207] using wordTrace_append hprefix tailTrace_4388207
  have hstable : (prefixWord ++ tailWord_4388207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388207).length < 2 ^ (prefixWord ++ tailWord_4388207).sum := by decide
  have hdescent : baseEnd_4388207 < baseStart_4388207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388228 : List Nat := [2, 3, 2, 1, 1, 4, 3, 2, 5]
def baseStart_4388228 : Nat := 118140960795 + 4388228 * 2 ^ 59
def prefixEnd_4388228 : Nat := 4983230072969 + 3 ^ 40 * 4388228 * 2
def baseEnd_4388228 : Nat := 250363353946462474607657

theorem tailTrace_4388228 : CollatzResearch.WordTrace tailWord_4388228 prefixEnd_4388228 250363353946462474607657 := by
  unfold tailWord_4388228
  simp only [CollatzResearch.WordTrace]
  refine ⟨80025911973103440260386669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106701215964137920347182225 80025911973103440260386669)
  ·
    refine ⟨30009716989913790097645001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80025911973103440260386669 30009716989913790097645001)
    ·
      refine ⟨22507287742435342573233751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30009716989913790097645001 22507287742435342573233751)
      ·
        refine ⟨33760931613653013859850627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22507287742435342573233751 33760931613653013859850627)
        ·
          refine ⟨50641397420479520789775941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33760931613653013859850627 50641397420479520789775941)
          ·
            refine ⟨9495262016339910148082989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50641397420479520789775941 9495262016339910148082989)
            ·
              refine ⟨3560723256127466305531121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9495262016339910148082989 3560723256127466305531121)
              ·
                refine ⟨2670542442095599729148341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3560723256127466305531121 2670542442095599729148341)
                ·
                  refine ⟨250363353946462474607657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2670542442095599729148341 250363353946462474607657)
                  ·
                    rfl

theorem cell23_4388228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 2, 5].length) (baseStart_4388228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4388228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4388228 prefixEnd_4388228 := by exact prefixLift 4388228
  have htrace : WordTrace (prefixWord ++ tailWord_4388228) baseStart_4388228 baseEnd_4388228 := by
    simpa [prefixWord, tailWord_4388228, baseEnd_4388228] using wordTrace_append hprefix tailTrace_4388228
  have hstable : (prefixWord ++ tailWord_4388228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388228).length < 2 ^ (prefixWord ++ tailWord_4388228).sum := by decide
  have hdescent : baseEnd_4388228 < baseStart_4388228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388381 : List Nat := [1, 4, 2, 2, 1, 1, 2, 1, 3, 2, 4]
def baseStart_4388381 : Nat := 118140960795 + 4388381 * 2 ^ 59
def prefixEnd_4388381 : Nat := 4983230072969 + 3 ^ 40 * 4388381 * 2
def baseEnd_4388381 : Nat := 2253348748058300172855709

theorem tailTrace_4388381 : CollatzResearch.WordTrace tailWord_4388381 prefixEnd_4388381 2253348748058300172855709 := by
  unfold tailWord_4388381
  simp only [CollatzResearch.WordTrace]
  refine ⟨160057404314652587651092997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106704936209768391767395331 160057404314652587651092997)
  ·
    refine ⟨30010763308997360184579937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160057404314652587651092997 30010763308997360184579937)
    ·
      refine ⟨22508072481748020138434953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30010763308997360184579937 22508072481748020138434953)
      ·
        refine ⟨16881054361311015103826215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22508072481748020138434953 16881054361311015103826215)
        ·
          refine ⟨25321581541966522655739323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16881054361311015103826215 25321581541966522655739323)
          ·
            refine ⟨37982372312949783983608985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25321581541966522655739323 37982372312949783983608985)
            ·
              refine ⟨28486779234712337987706739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37982372312949783983608985 28486779234712337987706739)
              ·
                refine ⟨42730168852068506981560109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28486779234712337987706739 42730168852068506981560109)
                ·
                  refine ⟨16023813319525690118085041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42730168852068506981560109 16023813319525690118085041)
                  ·
                    refine ⟨12017859989644267588563781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16023813319525690118085041 12017859989644267588563781)
                    ·
                      refine ⟨2253348748058300172855709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12017859989644267588563781 2253348748058300172855709)
                      ·
                        rfl

theorem cell23_4388381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_4388381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4388381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4388381 prefixEnd_4388381 := by exact prefixLift 4388381
  have htrace : WordTrace (prefixWord ++ tailWord_4388381) baseStart_4388381 baseEnd_4388381 := by
    simpa [prefixWord, tailWord_4388381, baseEnd_4388381] using wordTrace_append hprefix tailTrace_4388381
  have hstable : (prefixWord ++ tailWord_4388381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388381).length < 2 ^ (prefixWord ++ tailWord_4388381).sum := by decide
  have hdescent : baseEnd_4388381 < baseStart_4388381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388412 : List Nat := [2, 2, 2, 2, 4, 2, 2, 1, 2, 4]
def baseStart_4388412 : Nat := 118140960795 + 4388412 * 2 ^ 59
def prefixEnd_4388412 : Nat := 4983230072969 + 3 ^ 40 * 4388412 * 2
def baseEnd_4388412 : Nat := 751121555319529850522689

theorem tailTrace_4388412 : CollatzResearch.WordTrace tailWord_4388412 prefixEnd_4388412 751121555319529850522689 := by
  unfold tailWord_4388412
  simp only [CollatzResearch.WordTrace]
  refine ⟨80029267488770139972735745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106705689985026853296980993 80029267488770139972735745)
  ·
    refine ⟨60021950616577604979551809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80029267488770139972735745 60021950616577604979551809)
    ·
      refine ⟨45016462962433203734663857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60021950616577604979551809 45016462962433203734663857)
      ·
        refine ⟨33762347221824902800997893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45016462962433203734663857 33762347221824902800997893)
        ·
          refine ⟨6330440104092169275187105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33762347221824902800997893 6330440104092169275187105)
          ·
            refine ⟨4747830078069126956390329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6330440104092169275187105 4747830078069126956390329)
            ·
              refine ⟨3560872558551845217292747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4747830078069126956390329 3560872558551845217292747)
              ·
                refine ⟨5341308837827767825939121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3560872558551845217292747 5341308837827767825939121)
                ·
                  refine ⟨4005981628370825869454341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5341308837827767825939121 4005981628370825869454341)
                  ·
                    refine ⟨751121555319529850522689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4005981628370825869454341 751121555319529850522689)
                    ·
                      rfl

theorem cell23_4388412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 2, 4].length) (baseStart_4388412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4388412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4388412 prefixEnd_4388412 := by exact prefixLift 4388412
  have htrace : WordTrace (prefixWord ++ tailWord_4388412) baseStart_4388412 baseEnd_4388412 := by
    simpa [prefixWord, tailWord_4388412, baseEnd_4388412] using wordTrace_append hprefix tailTrace_4388412
  have hstable : (prefixWord ++ tailWord_4388412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388412).length < 2 ^ (prefixWord ++ tailWord_4388412).sum := by decide
  have hdescent : baseEnd_4388412 < baseStart_4388412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388422 : List Nat := [6, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3]
def baseStart_4388422 : Nat := 118140960795 + 4388422 * 2 ^ 59
def prefixEnd_4388422 : Nat := 4983230072969 + 3 ^ 40 * 4388422 * 2
def baseEnd_4388422 : Nat := 2253369800765134512443021

theorem tailTrace_4388422 : CollatzResearch.WordTrace tailWord_4388422 prefixEnd_4388422 2253369800765134512443021 := by
  unfold tailWord_4388422
  simp only [CollatzResearch.WordTrace]
  refine ⟨5001840615859501614166735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 106705933138336034435557013 5001840615859501614166735)
  ·
    refine ⟨7502760923789252421250103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5001840615859501614166735 7502760923789252421250103)
    ·
      refine ⟨11254141385683878631875155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7502760923789252421250103 11254141385683878631875155)
      ·
        refine ⟨16881212078525817947812733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11254141385683878631875155 16881212078525817947812733)
        ·
          refine ⟨6330454529447181730429775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16881212078525817947812733 6330454529447181730429775)
          ·
            refine ⟨9495681794170772595644663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6330454529447181730429775 9495681794170772595644663)
            ·
              refine ⟨14243522691256158893466995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9495681794170772595644663 14243522691256158893466995)
              ·
                refine ⟨21365284036884238340200493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14243522691256158893466995 21365284036884238340200493)
                ·
                  refine ⟨8011981513831589377575185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21365284036884238340200493 8011981513831589377575185)
                  ·
                    refine ⟨6008986135373692033181389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8011981513831589377575185 6008986135373692033181389)
                    ·
                      refine ⟨2253369800765134512443021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6008986135373692033181389 2253369800765134512443021)
                      ·
                        rfl

theorem cell23_4388422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_4388422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4388422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4388422 prefixEnd_4388422 := by exact prefixLift 4388422
  have htrace : WordTrace (prefixWord ++ tailWord_4388422) baseStart_4388422 baseEnd_4388422 := by
    simpa [prefixWord, tailWord_4388422, baseEnd_4388422] using wordTrace_append hprefix tailTrace_4388422
  have hstable : (prefixWord ++ tailWord_4388422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388422).length < 2 ^ (prefixWord ++ tailWord_4388422).sum := by decide
  have hdescent : baseEnd_4388422 < baseStart_4388422 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388424 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 1, 1, 10]
def baseStart_4388424 : Nat := 118140960795 + 4388424 * 2 ^ 59
def prefixEnd_4388424 : Nat := 4983230072969 + 3 ^ 40 * 4388424 * 2
def baseEnd_4388424 : Nat := 2253370827726443504618011

theorem tailTrace_4388424 : CollatzResearch.WordTrace tailWord_4388424 prefixEnd_4388424 2253370827726443504618011 := by
  unfold tailWord_4388424
  simp only [CollatzResearch.WordTrace]
  refine ⟨80029486326748402997454163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106705981768997870663272217 80029486326748402997454163)
  ·
    refine ⟨120044229490122604496181245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80029486326748402997454163 120044229490122604496181245)
    ·
      refine ⟨45016586058795976686067967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120044229490122604496181245 45016586058795976686067967)
      ·
        refine ⟨67524879088193965029101951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45016586058795976686067967 67524879088193965029101951)
        ·
          refine ⟨101287318632290947543652927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67524879088193965029101951 101287318632290947543652927)
          ·
            refine ⟨151930977948436421315479391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101287318632290947543652927 151930977948436421315479391)
            ·
              refine ⟨227896466922654631973219087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151930977948436421315479391 227896466922654631973219087)
              ·
                refine ⟨341844700383981947959828631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 227896466922654631973219087 341844700383981947959828631)
                ·
                  refine ⟨512767050575972921939742947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 341844700383981947959828631 512767050575972921939742947)
                  ·
                    refine ⟨769150575863959382909614421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 512767050575972921939742947 769150575863959382909614421)
                    ·
                      refine ⟨2253370827726443504618011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 769150575863959382909614421 2253370827726443504618011)
                      ·
                        rfl

theorem cell23_4388424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_4388424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4388424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4388424 prefixEnd_4388424 := by exact prefixLift 4388424
  have htrace : WordTrace (prefixWord ++ tailWord_4388424) baseStart_4388424 baseEnd_4388424 := by
    simpa [prefixWord, tailWord_4388424, baseEnd_4388424] using wordTrace_append hprefix tailTrace_4388424
  have hstable : (prefixWord ++ tailWord_4388424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388424).length < 2 ^ (prefixWord ++ tailWord_4388424).sum := by decide
  have hdescent : baseEnd_4388424 < baseStart_4388424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388475 : List Nat := [1, 1, 1, 1, 1, 4, 3, 5, 2, 2, 2]
def baseStart_4388475 : Nat := 118140960795 + 4388475 * 2 ^ 59
def prefixEnd_4388475 : Nat := 4983230072969 + 3 ^ 40 * 4388475 * 2
def baseEnd_4388475 : Nat := 2253397015239822805080277

theorem tailTrace_4388475 : CollatzResearch.WordTrace tailWord_4388475 prefixEnd_4388475 2253397015239822805080277 := by
  unfold tailWord_4388475
  simp only [CollatzResearch.WordTrace]
  refine ⟨160060832776312041705014879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106707221850874694470009919 160060832776312041705014879)
  ·
    refine ⟨240091249164468062557522319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160060832776312041705014879 240091249164468062557522319)
    ·
      refine ⟨360136873746702093836283479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240091249164468062557522319 360136873746702093836283479)
      ·
        refine ⟨540205310620053140754425219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 360136873746702093836283479 540205310620053140754425219)
        ·
          refine ⟨810307965930079711131637829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 540205310620053140754425219 810307965930079711131637829)
          ·
            refine ⟨151932743611889945837182093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 810307965930079711131637829 151932743611889945837182093)
            ·
              refine ⟨56974778854458729688943285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 151932743611889945837182093 56974778854458729688943285)
              ·
                refine ⟨5341385517605505908338433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56974778854458729688943285 5341385517605505908338433)
                ·
                  refine ⟨4006039138204129431253825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5341385517605505908338433 4006039138204129431253825)
                  ·
                    refine ⟨3004529353653097073440369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4006039138204129431253825 3004529353653097073440369)
                    ·
                      refine ⟨2253397015239822805080277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3004529353653097073440369 2253397015239822805080277)
                      ·
                        rfl

theorem cell23_4388475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 2, 2, 2].length) (baseStart_4388475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4388475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4388475 prefixEnd_4388475 := by exact prefixLift 4388475
  have htrace : WordTrace (prefixWord ++ tailWord_4388475) baseStart_4388475 baseEnd_4388475 := by
    simpa [prefixWord, tailWord_4388475, baseEnd_4388475] using wordTrace_append hprefix tailTrace_4388475
  have hstable : (prefixWord ++ tailWord_4388475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388475).length < 2 ^ (prefixWord ++ tailWord_4388475).sum := by decide
  have hdescent : baseEnd_4388475 < baseStart_4388475 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388481 : List Nat := [1, 2, 4, 2, 1, 2, 1, 1, 9]
def baseStart_4388481 : Nat := 118140960795 + 4388481 * 2 ^ 59
def prefixEnd_4388481 : Nat := 4983230072969 + 3 ^ 40 * 4388481 * 2
def baseEnd_4388481 : Nat := 250377788458194420178361

theorem tailTrace_4388481 : CollatzResearch.WordTrace tailWord_4388481 prefixEnd_4388481 250377788458194420178361 := by
  unfold tailWord_4388481
  simp only [CollatzResearch.WordTrace]
  refine ⟨160061051614290304729733297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106707367742860203153155531 160061051614290304729733297)
  ·
    refine ⟨120045788710717728547299973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160061051614290304729733297 120045788710717728547299973)
    ·
      refine ⟨22508585383259574102618745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120045788710717728547299973 22508585383259574102618745)
      ·
        refine ⟨16881439037444680576964059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22508585383259574102618745 16881439037444680576964059)
        ·
          refine ⟨25322158556167020865446089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16881439037444680576964059 25322158556167020865446089)
          ·
            refine ⟨18991618917125265649084567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25322158556167020865446089 18991618917125265649084567)
            ·
              refine ⟨28487428375687898473626851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18991618917125265649084567 28487428375687898473626851)
              ·
                refine ⟨42731142563531847710440277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28487428375687898473626851 42731142563531847710440277)
                ·
                  refine ⟨250377788458194420178361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 42731142563531847710440277 250377788458194420178361)
                  ·
                    rfl

theorem cell23_4388481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 9].length) (baseStart_4388481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4388481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4388481 prefixEnd_4388481 := by exact prefixLift 4388481
  have htrace : WordTrace (prefixWord ++ tailWord_4388481) baseStart_4388481 baseEnd_4388481 := by
    simpa [prefixWord, tailWord_4388481, baseEnd_4388481] using wordTrace_append hprefix tailTrace_4388481
  have hstable : (prefixWord ++ tailWord_4388481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388481).length < 2 ^ (prefixWord ++ tailWord_4388481).sum := by decide
  have hdescent : baseEnd_4388481 < baseStart_4388481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388491 : List Nat := [1, 1, 1, 1, 4, 1, 3, 2, 1, 5, 3]
def baseStart_4388491 : Nat := 118140960795 + 4388491 * 2 ^ 59
def prefixEnd_4388491 : Nat := 4983230072969 + 3 ^ 40 * 4388491 * 2
def baseEnd_4388491 : Nat := 2253405230930294742480203

theorem tailTrace_4388491 : CollatzResearch.WordTrace tailWord_4388491 prefixEnd_4388491 2253405230930294742480203 := by
  unfold tailWord_4388491
  simp only [CollatzResearch.WordTrace]
  refine ⟨160061416344254076437597327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106707610896169384291731551 160061416344254076437597327)
  ·
    refine ⟨240092124516381114656395991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160061416344254076437597327 240092124516381114656395991)
    ·
      refine ⟨360138186774571671984593987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240092124516381114656395991 360138186774571671984593987)
      ·
        refine ⟨540207280161857507976890981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 360138186774571671984593987 540207280161857507976890981)
        ·
          refine ⟨101288865030348282745667059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 540207280161857507976890981 101288865030348282745667059)
          ·
            refine ⟨151933297545522424118500589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101288865030348282745667059 151933297545522424118500589)
            ·
              refine ⟨56974986579570909044437721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 151933297545522424118500589 56974986579570909044437721)
              ·
                refine ⟨42731239934678181783328291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56974986579570909044437721 42731239934678181783328291)
                ·
                  refine ⟨64096859902017272674992437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42731239934678181783328291 64096859902017272674992437)
                  ·
                    refine ⟨6009080615814119313280541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 64096859902017272674992437 6009080615814119313280541)
                    ·
                      refine ⟨2253405230930294742480203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6009080615814119313280541 2253405230930294742480203)
                      ·
                        rfl

theorem cell23_4388491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 5, 3].length) (baseStart_4388491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4388491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4388491 prefixEnd_4388491 := by exact prefixLift 4388491
  have htrace : WordTrace (prefixWord ++ tailWord_4388491) baseStart_4388491 baseEnd_4388491 := by
    simpa [prefixWord, tailWord_4388491, baseEnd_4388491] using wordTrace_append hprefix tailTrace_4388491
  have hstable : (prefixWord ++ tailWord_4388491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388491).length < 2 ^ (prefixWord ++ tailWord_4388491).sum := by decide
  have hdescent : baseEnd_4388491 < baseStart_4388491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388526 : List Nat := [4, 1, 4, 1, 3, 1, 1, 1, 1, 4, 2]
def baseStart_4388526 : Nat := 118140960795 + 4388526 * 2 ^ 59
def prefixEnd_4388526 : Nat := 4983230072969 + 3 ^ 40 * 4388526 * 2
def baseEnd_4388526 : Nat := 2253423202753202105542543

theorem tailTrace_4388526 : CollatzResearch.WordTrace tailWord_4388526 prefixEnd_4388526 2253423202753202105542543 := by
  unfold tailWord_4388526
  simp only [CollatzResearch.WordTrace]
  refine ⟨20007836612390909676890179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106708461932751518276747621 20007836612390909676890179)
  ·
    refine ⟨30011754918586364515335269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20007836612390909676890179 30011754918586364515335269)
    ·
      refine ⟨5627204047234943346625363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30011754918586364515335269 5627204047234943346625363)
      ·
        refine ⟨8440806070852415019938045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5627204047234943346625363 8440806070852415019938045)
        ·
          refine ⟨3165302276569655632476767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8440806070852415019938045 3165302276569655632476767)
          ·
            refine ⟨4747953414854483448715151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3165302276569655632476767 4747953414854483448715151)
            ·
              refine ⟨7121930122281725173072727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4747953414854483448715151 7121930122281725173072727)
              ·
                refine ⟨10682895183422587759609091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7121930122281725173072727 10682895183422587759609091)
                ·
                  refine ⟨16024342775133881639413637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10682895183422587759609091 16024342775133881639413637)
                  ·
                    refine ⟨3004564270337602807390057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16024342775133881639413637 3004564270337602807390057)
                    ·
                      refine ⟨2253423202753202105542543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3004564270337602807390057 2253423202753202105542543)
                      ·
                        rfl

theorem cell23_4388526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_4388526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4388526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4388526 prefixEnd_4388526 := by exact prefixLift 4388526
  have htrace : WordTrace (prefixWord ++ tailWord_4388526) baseStart_4388526 baseEnd_4388526 := by
    simpa [prefixWord, tailWord_4388526, baseEnd_4388526] using wordTrace_append hprefix tailTrace_4388526
  have hstable : (prefixWord ++ tailWord_4388526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388526).length < 2 ^ (prefixWord ++ tailWord_4388526).sum := by decide
  have hdescent : baseEnd_4388526 < baseStart_4388526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388531 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 4]
def baseStart_4388531 : Nat := 118140960795 + 4388531 * 2 ^ 59
def prefixEnd_4388531 : Nat := 4983230072969 + 3 ^ 40 * 4388531 * 2
def baseEnd_4388531 : Nat := 2253425770156474585980019

theorem tailTrace_4388531 : CollatzResearch.WordTrace tailWord_4388531 prefixEnd_4388531 2253425770156474585980019 := by
  unfold tailWord_4388531
  simp only [CollatzResearch.WordTrace]
  refine ⟨160062875264109163269053447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106708583509406108846035631 160062875264109163269053447)
  ·
    refine ⟨240094312896163744903580171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160062875264109163269053447 240094312896163744903580171)
    ·
      refine ⟨360141469344245617355370257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240094312896163744903580171 360141469344245617355370257)
      ·
        refine ⟨270106102008184213016527693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 360141469344245617355370257 270106102008184213016527693)
        ·
          refine ⟨101289788253069079881197885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 270106102008184213016527693 101289788253069079881197885)
          ·
            refine ⟨37983670594900904955449207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101289788253069079881197885 37983670594900904955449207)
            ·
              refine ⟨56975505892351357433173811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37983670594900904955449207 56975505892351357433173811)
              ·
                refine ⟨85463258838527036149760717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56975505892351357433173811 85463258838527036149760717)
                ·
                  refine ⟨32048722064447638556160269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85463258838527036149760717 32048722064447638556160269)
                  ·
                    refine ⟨12018270774167864458560101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32048722064447638556160269 12018270774167864458560101)
                    ·
                      refine ⟨2253425770156474585980019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12018270774167864458560101 2253425770156474585980019)
                      ·
                        rfl

theorem cell23_4388531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 4].length) (baseStart_4388531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4388531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4388531 prefixEnd_4388531 := by exact prefixLift 4388531
  have htrace : WordTrace (prefixWord ++ tailWord_4388531) baseStart_4388531 baseEnd_4388531 := by
    simpa [prefixWord, tailWord_4388531, baseEnd_4388531] using wordTrace_append hprefix tailTrace_4388531
  have hstable : (prefixWord ++ tailWord_4388531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388531).length < 2 ^ (prefixWord ++ tailWord_4388531).sum := by decide
  have hdescent : baseEnd_4388531 < baseStart_4388531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388541 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 2, 8]
def baseStart_4388541 : Nat := 118140960795 + 4388541 * 2 ^ 59
def prefixEnd_4388541 : Nat := 4983230072969 + 3 ^ 40 * 4388541 * 2
def baseEnd_4388541 : Nat := 751143634987673182284991

theorem tailTrace_4388541 : CollatzResearch.WordTrace tailWord_4388541 prefixEnd_4388541 751143634987673182284991 := by
  unfold tailWord_4388541
  simp only [CollatzResearch.WordTrace]
  refine ⟨160063239994072934976917477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106708826662715289984611651 160063239994072934976917477)
  ·
    refine ⟨30011857498888675308172027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160063239994072934976917477 30011857498888675308172027)
    ·
      refine ⟨45017786248333012962258041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30011857498888675308172027 45017786248333012962258041)
      ·
        refine ⟨33763339686249759721693531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45017786248333012962258041 33763339686249759721693531)
        ·
          refine ⟨50645009529374639582540297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33763339686249759721693531 50645009529374639582540297)
          ·
            refine ⟨37983757147030979686905223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50645009529374639582540297 37983757147030979686905223)
            ·
              refine ⟨56975635720546469530357835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37983757147030979686905223 56975635720546469530357835)
              ·
                refine ⟨85463453580819704295536753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56975635720546469530357835 85463453580819704295536753)
                ·
                  refine ⟨64097590185614778221652565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85463453580819704295536753 64097590185614778221652565)
                  ·
                    refine ⟨751143634987673182284991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 64097590185614778221652565 751143634987673182284991)
                    ·
                      rfl

theorem cell23_4388541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_4388541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4388541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4388541 prefixEnd_4388541 := by exact prefixLift 4388541
  have htrace : WordTrace (prefixWord ++ tailWord_4388541) baseStart_4388541 baseEnd_4388541 := by
    simpa [prefixWord, tailWord_4388541, baseEnd_4388541] using wordTrace_append hprefix tailTrace_4388541
  have hstable : (prefixWord ++ tailWord_4388541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388541).length < 2 ^ (prefixWord ++ tailWord_4388541).sum := by decide
  have hdescent : baseEnd_4388541 < baseStart_4388541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388548 : List Nat := [2, 3, 3, 1, 1, 1, 1, 3, 1, 3, 4]
def baseStart_4388548 : Nat := 118140960795 + 4388548 * 2 ^ 59
def prefixEnd_4388548 : Nat := 4983230072969 + 3 ^ 40 * 4388548 * 2
def baseEnd_4388548 : Nat := 2253434499327601019467441

theorem tailTrace_4388548 : CollatzResearch.WordTrace tailWord_4388548 prefixEnd_4388548 2253434499327601019467441 := by
  unfold tailWord_4388548
  simp only [CollatzResearch.WordTrace]
  refine ⟨80031747652523787586211149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106708996870031716781614865 80031747652523787586211149)
  ·
    refine ⟨30011905369696420344829181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80031747652523787586211149 30011905369696420344829181)
    ·
      refine ⟨11254464513636157629310943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30011905369696420344829181 11254464513636157629310943)
      ·
        refine ⟨16881696770454236443966415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11254464513636157629310943 16881696770454236443966415)
        ·
          refine ⟨25322545155681354665949623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16881696770454236443966415 25322545155681354665949623)
          ·
            refine ⟨37983817733522031998924435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25322545155681354665949623 37983817733522031998924435)
            ·
              refine ⟨56975726600283047998386653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37983817733522031998924435 56975726600283047998386653)
              ·
                refine ⟨21365897475106142999394995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56975726600283047998386653 21365897475106142999394995)
                ·
                  refine ⟨32048846212659214499092493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21365897475106142999394995 32048846212659214499092493)
                  ·
                    refine ⟨12018317329747205437159685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32048846212659214499092493 12018317329747205437159685)
                    ·
                      refine ⟨2253434499327601019467441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12018317329747205437159685 2253434499327601019467441)
                      ·
                        rfl

theorem cell23_4388548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_4388548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4388548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4388548 prefixEnd_4388548 := by exact prefixLift 4388548
  have htrace : WordTrace (prefixWord ++ tailWord_4388548) baseStart_4388548 baseEnd_4388548 := by
    simpa [prefixWord, tailWord_4388548, baseEnd_4388548] using wordTrace_append hprefix tailTrace_4388548
  have hstable : (prefixWord ++ tailWord_4388548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388548).length < 2 ^ (prefixWord ++ tailWord_4388548).sum := by decide
  have hdescent : baseEnd_4388548 < baseStart_4388548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388566 : List Nat := [5, 2, 1, 3, 1, 1, 3, 2, 5]
def baseStart_4388566 : Nat := 118140960795 + 4388566 * 2 ^ 59
def prefixEnd_4388566 : Nat := 4983230072969 + 3 ^ 40 * 4388566 * 2
def baseEnd_4388566 : Nat := 250382637997709105449151

theorem tailTrace_4388566 : CollatzResearch.WordTrace tailWord_4388566 prefixEnd_4388566 250382637997709105449151 := by
  unfold tailWord_4388566
  simp only [CollatzResearch.WordTrace]
  refine ⟨10004009488686397765411097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106709434545988242831051701 10004009488686397765411097)
  ·
    refine ⟨7503007116514798324058323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10004009488686397765411097 7503007116514798324058323)
    ·
      refine ⟨11254510674772197486087485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7503007116514798324058323 11254510674772197486087485)
      ·
        refine ⟨4220441503039574057282807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11254510674772197486087485 4220441503039574057282807)
        ·
          refine ⟨6330662254559361085924211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4220441503039574057282807 6330662254559361085924211)
          ·
            refine ⟨9495993381839041628886317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6330662254559361085924211 9495993381839041628886317)
            ·
              refine ⟨3560997518189640610832369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9495993381839041628886317 3560997518189640610832369)
              ·
                refine ⟨2670748138642230458124277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3560997518189640610832369 2670748138642230458124277)
                ·
                  refine ⟨250382637997709105449151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2670748138642230458124277 250382637997709105449151)
                  ·
                    rfl

theorem cell23_4388566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_4388566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4388566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4388566 prefixEnd_4388566 := by exact prefixLift 4388566
  have htrace : WordTrace (prefixWord ++ tailWord_4388566) baseStart_4388566 baseEnd_4388566 := by
    simpa [prefixWord, tailWord_4388566, baseEnd_4388566] using wordTrace_append hprefix tailTrace_4388566
  have hstable : (prefixWord ++ tailWord_4388566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388566).length < 2 ^ (prefixWord ++ tailWord_4388566).sum := by decide
  have hdescent : baseEnd_4388566 < baseStart_4388566 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388626 : List Nat := [3, 2, 4, 1, 1, 1, 4, 2, 1, 4]
def baseStart_4388626 : Nat := 118140960795 + 4388626 * 2 ^ 59
def prefixEnd_4388626 : Nat := 4983230072969 + 3 ^ 40 * 4388626 * 2
def baseEnd_4388626 : Nat := 751158183606217238097361

theorem tailTrace_4388626 : CollatzResearch.WordTrace tailWord_4388626 prefixEnd_4388626 751158183606217238097361 := by
  unfold tailWord_4388626
  simp only [CollatzResearch.WordTrace]
  refine ⟨40016585049691248623440433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106710893465843329662507821 40016585049691248623440433)
  ·
    refine ⟨30012438787268436467580325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40016585049691248623440433 30012438787268436467580325)
    ·
      refine ⟨5627332272612831837671311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30012438787268436467580325 5627332272612831837671311)
      ·
        refine ⟨8440998408919247756506967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5627332272612831837671311 8440998408919247756506967)
        ·
          refine ⟨12661497613378871634760451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8440998408919247756506967 12661497613378871634760451)
          ·
            refine ⟨18992246420068307452140677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12661497613378871634760451 18992246420068307452140677)
            ·
              refine ⟨3561046203762807647276377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18992246420068307452140677 3561046203762807647276377)
              ·
                refine ⟨2670784652822105735457283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3561046203762807647276377 2670784652822105735457283)
                ·
                  refine ⟨4006176979233158603185925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2670784652822105735457283 4006176979233158603185925)
                  ·
                    refine ⟨751158183606217238097361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4006176979233158603185925 751158183606217238097361)
                    ·
                      rfl

theorem cell23_4388626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_4388626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4388626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4388626 prefixEnd_4388626 := by exact prefixLift 4388626
  have htrace : WordTrace (prefixWord ++ tailWord_4388626) baseStart_4388626 baseEnd_4388626 := by
    simpa [prefixWord, tailWord_4388626, baseEnd_4388626] using wordTrace_append hprefix tailTrace_4388626
  have hstable : (prefixWord ++ tailWord_4388626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388626).length < 2 ^ (prefixWord ++ tailWord_4388626).sum := by decide
  have hdescent : baseEnd_4388626 < baseStart_4388626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388659 : List Nat := [1, 1, 1, 2, 7, 2, 1, 1, 2, 3, 2]
def baseStart_4388659 : Nat := 118140960795 + 4388659 * 2 ^ 59
def prefixEnd_4388659 : Nat := 4983230072969 + 3 ^ 40 * 4388659 * 2
def baseEnd_4388659 : Nat := 2253491495680250085179431

theorem tailTrace_4388659 : CollatzResearch.WordTrace tailWord_4388659 prefixEnd_4388659 2253491495680250085179431 := by
  unfold tailWord_4388659
  simp only [CollatzResearch.WordTrace]
  refine ⟨160067543807645441129713031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106711695871763627419808687 160067543807645441129713031)
  ·
    refine ⟨240101315711468161694569547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160067543807645441129713031 240101315711468161694569547)
    ·
      refine ⟨360151973567202242541854321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240101315711468161694569547 360151973567202242541854321)
      ·
        refine ⟨270113980175401681906390741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 360151973567202242541854321 270113980175401681906390741)
        ·
          refine ⟨6330796410360976919681033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 270113980175401681906390741 6330796410360976919681033)
          ·
            refine ⟨4748097307770732689760775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6330796410360976919681033 4748097307770732689760775)
            ·
              refine ⟨7122145961656099034641163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4748097307770732689760775 7122145961656099034641163)
              ·
                refine ⟨10683218942484148551961745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7122145961656099034641163 10683218942484148551961745)
                ·
                  refine ⟨8012414206863111413971309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10683218942484148551961745 8012414206863111413971309)
                  ·
                    refine ⟨3004655327573666780239241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8012414206863111413971309 3004655327573666780239241)
                    ·
                      refine ⟨2253491495680250085179431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3004655327573666780239241 2253491495680250085179431)
                      ·
                        rfl

theorem cell23_4388659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 3, 2].length) (baseStart_4388659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4388659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4388659 prefixEnd_4388659 := by exact prefixLift 4388659
  have htrace : WordTrace (prefixWord ++ tailWord_4388659) baseStart_4388659 baseEnd_4388659 := by
    simpa [prefixWord, tailWord_4388659, baseEnd_4388659] using wordTrace_append hprefix tailTrace_4388659
  have hstable : (prefixWord ++ tailWord_4388659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388659).length < 2 ^ (prefixWord ++ tailWord_4388659).sum := by decide
  have hdescent : baseEnd_4388659 < baseStart_4388659 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388669 : List Nat := [1, 4, 1, 4, 1, 3, 2, 1, 1, 5]
def baseStart_4388669 : Nat := 118140960795 + 4388669 * 2 ^ 59
def prefixEnd_4388669 : Nat := 4983230072969 + 3 ^ 40 * 4388669 * 2
def baseEnd_4388669 : Nat := 751165543495598348684795

theorem tailTrace_4388669 : CollatzResearch.WordTrace tailWord_4388669 prefixEnd_4388669 751165543495598348684795 := by
  unfold tailWord_4388669
  simp only [CollatzResearch.WordTrace]
  refine ⟨160067908537609212837577061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106711939025072808558384707 160067908537609212837577061)
  ·
    refine ⟨30012732850801727407045699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160067908537609212837577061 30012732850801727407045699)
    ·
      refine ⟨45019099276202591110568549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30012732850801727407045699 45019099276202591110568549)
      ·
        refine ⟨8441081114287985833231603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45019099276202591110568549 8441081114287985833231603)
        ·
          refine ⟨12661621671431978749847405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8441081114287985833231603 12661621671431978749847405)
          ·
            refine ⟨4748108126786992031192777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12661621671431978749847405 4748108126786992031192777)
            ·
              refine ⟨3561081095090244023394583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4748108126786992031192777 3561081095090244023394583)
              ·
                refine ⟨5341621642635366035091875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3561081095090244023394583 5341621642635366035091875)
                ·
                  refine ⟨8012432463953049052637813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5341621642635366035091875 8012432463953049052637813)
                  ·
                    refine ⟨751165543495598348684795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8012432463953049052637813 751165543495598348684795)
                    ·
                      rfl

theorem cell23_4388669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 1, 5].length) (baseStart_4388669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4388669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4388669 prefixEnd_4388669 := by exact prefixLift 4388669
  have htrace : WordTrace (prefixWord ++ tailWord_4388669) baseStart_4388669 baseEnd_4388669 := by
    simpa [prefixWord, tailWord_4388669, baseEnd_4388669] using wordTrace_append hprefix tailTrace_4388669
  have hstable : (prefixWord ++ tailWord_4388669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388669).length < 2 ^ (prefixWord ++ tailWord_4388669).sum := by decide
  have hdescent : baseEnd_4388669 < baseStart_4388669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388689 : List Nat := [1, 2, 2, 1, 5, 2, 2, 1, 3, 2, 2]
def baseStart_4388689 : Nat := 118140960795 + 4388689 * 2 ^ 59
def prefixEnd_4388689 : Nat := 4983230072969 + 3 ^ 40 * 4388689 * 2
def baseEnd_4388689 : Nat := 2253506900099884967804293

theorem tailTrace_4388689 : CollatzResearch.WordTrace tailWord_4388689 prefixEnd_4388689 2253506900099884967804293 := by
  unfold tailWord_4388689
  simp only [CollatzResearch.WordTrace]
  refine ⟨160068637997536756253305121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106712425331691170835536747 160068637997536756253305121)
  ·
    refine ⟨120051478498152567189978841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160068637997536756253305121 120051478498152567189978841)
    ·
      refine ⟨90038608873614425392484131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120051478498152567189978841 90038608873614425392484131)
      ·
        refine ⟨135057913310421638088726197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90038608873614425392484131 135057913310421638088726197)
        ·
          refine ⟨12661679372852028570818081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 135057913310421638088726197 12661679372852028570818081)
          ·
            refine ⟨9496259529639021428113561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12661679372852028570818081 9496259529639021428113561)
            ·
              refine ⟨7122194647229266071085171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9496259529639021428113561 7122194647229266071085171)
              ·
                refine ⟨10683291970843899106627757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7122194647229266071085171 10683291970843899106627757)
                ·
                  refine ⟨4006234489066462164985409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10683291970843899106627757 4006234489066462164985409)
                  ·
                    refine ⟨3004675866799846623739057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4006234489066462164985409 3004675866799846623739057)
                    ·
                      refine ⟨2253506900099884967804293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3004675866799846623739057 2253506900099884967804293)
                      ·
                        rfl

theorem cell23_4388689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 3, 2, 2].length) (baseStart_4388689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4388689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4388689 prefixEnd_4388689 := by exact prefixLift 4388689
  have htrace : WordTrace (prefixWord ++ tailWord_4388689) baseStart_4388689 baseEnd_4388689 := by
    simpa [prefixWord, tailWord_4388689, baseEnd_4388689] using wordTrace_append hprefix tailTrace_4388689
  have hstable : (prefixWord ++ tailWord_4388689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388689).length < 2 ^ (prefixWord ++ tailWord_4388689).sum := by decide
  have hdescent : baseEnd_4388689 < baseStart_4388689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388748 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 3, 3, 5]
def baseStart_4388748 : Nat := 118140960795 + 4388748 * 2 ^ 59
def prefixEnd_4388748 : Nat := 4983230072969 + 3 ^ 40 * 4388748 * 2
def baseEnd_4388748 : Nat := 2253537195458500236966521

theorem tailTrace_4388748 : CollatzResearch.WordTrace tailWord_4388748 prefixEnd_4388748 2253537195458500236966521 := by
  unfold tailWord_4388748
  simp only [CollatzResearch.WordTrace]
  refine ⟨80035394952161504664851449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106713859936215339553135265 80035394952161504664851449)
  ·
    refine ⟨60026546214121128498638587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80035394952161504664851449 60026546214121128498638587)
    ·
      refine ⟨90039819321181692747957881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60026546214121128498638587 90039819321181692747957881)
      ·
        refine ⟨67529864490886269560968411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90039819321181692747957881 67529864490886269560968411)
        ·
          refine ⟨101294796736329404341452617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67529864490886269560968411 101294796736329404341452617)
          ·
            refine ⟨75971097552247053256089463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101294796736329404341452617 75971097552247053256089463)
            ·
              refine ⟨113956646328370579884134195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75971097552247053256089463 113956646328370579884134195)
              ·
                refine ⟨170934969492555869826201293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113956646328370579884134195 170934969492555869826201293)
                ·
                  refine ⟨64100613559708451184825485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 170934969492555869826201293 64100613559708451184825485)
                  ·
                    refine ⟨24037730084890669194309557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64100613559708451184825485 24037730084890669194309557)
                    ·
                      refine ⟨2253537195458500236966521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24037730084890669194309557 2253537195458500236966521)
                      ·
                        rfl

theorem cell23_4388748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_4388748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4388748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4388748 prefixEnd_4388748 := by exact prefixLift 4388748
  have htrace : WordTrace (prefixWord ++ tailWord_4388748) baseStart_4388748 baseEnd_4388748 := by
    simpa [prefixWord, tailWord_4388748, baseEnd_4388748] using wordTrace_append hprefix tailTrace_4388748
  have hstable : (prefixWord ++ tailWord_4388748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388748).length < 2 ^ (prefixWord ++ tailWord_4388748).sum := by decide
  have hdescent : baseEnd_4388748 < baseStart_4388748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388756 : List Nat := [2, 4, 2, 1, 1, 2, 4, 1, 2, 1, 3]
def baseStart_4388756 : Nat := 118140960795 + 4388756 * 2 ^ 59
def prefixEnd_4388756 : Nat := 4983230072969 + 3 ^ 40 * 4388756 * 2
def baseEnd_4388756 : Nat := 2253541303303736205666485

theorem tailTrace_4388756 : CollatzResearch.WordTrace tailWord_4388756 prefixEnd_4388756 2253541303303736205666485 := by
  unfold tailWord_4388756
  simp only [CollatzResearch.WordTrace]
  refine ⟨80035540844147013347997061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106714054458862684463996081 80035540844147013347997061)
  ·
    refine ⟨15006663908277565002749449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80035540844147013347997061 15006663908277565002749449)
    ·
      refine ⟨11254997931208173752062087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15006663908277565002749449 11254997931208173752062087)
      ·
        refine ⟨16882496896812260628093131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11254997931208173752062087 16882496896812260628093131)
        ·
          refine ⟨25323745345218390942139697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16882496896812260628093131 25323745345218390942139697)
          ·
            refine ⟨18992809008913793206604773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25323745345218390942139697 18992809008913793206604773)
            ·
              refine ⟨3561151689171336226238395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18992809008913793206604773 3561151689171336226238395)
              ·
                refine ⟨5341727533757004339357593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3561151689171336226238395 5341727533757004339357593)
                ·
                  refine ⟨4006295650317753254518195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5341727533757004339357593 4006295650317753254518195)
                  ·
                    refine ⟨6009443475476629881777293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4006295650317753254518195 6009443475476629881777293)
                    ·
                      refine ⟨2253541303303736205666485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6009443475476629881777293 2253541303303736205666485)
                      ·
                        rfl

theorem cell23_4388756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_4388756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4388756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4388756 prefixEnd_4388756 := by exact prefixLift 4388756
  have htrace : WordTrace (prefixWord ++ tailWord_4388756) baseStart_4388756 baseEnd_4388756 := by
    simpa [prefixWord, tailWord_4388756, baseEnd_4388756] using wordTrace_append hprefix tailTrace_4388756
  have hstable : (prefixWord ++ tailWord_4388756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388756).length < 2 ^ (prefixWord ++ tailWord_4388756).sum := by decide
  have hdescent : baseEnd_4388756 < baseStart_4388756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388765 : List Nat := [1, 4, 2, 1, 2, 2, 1, 2, 2, 1, 5]
def baseStart_4388765 : Nat := 118140960795 + 4388765 * 2 ^ 59
def prefixEnd_4388765 : Nat := 4983230072969 + 3 ^ 40 * 4388765 * 2
def baseEnd_4388765 : Nat := 2253545924629626670453943

theorem tailTrace_4388765 : CollatzResearch.WordTrace tailWord_4388765 prefixEnd_4388765 2253545924629626670453943 := by
  unfold tailWord_4388765
  simp only [CollatzResearch.WordTrace]
  refine ⟨160071409945261421233071749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106714273296840947488714499 160071409945261421233071749)
  ·
    refine ⟨30013389364736516481200953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160071409945261421233071749 30013389364736516481200953)
    ·
      refine ⟨22510042023552387360900715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30013389364736516481200953 22510042023552387360900715)
      ·
        refine ⟨33765063035328581041351073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22510042023552387360900715 33765063035328581041351073)
        ·
          refine ⟨25323797276496435781013305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33765063035328581041351073 25323797276496435781013305)
          ·
            refine ⟨18992847957372326835759979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25323797276496435781013305 18992847957372326835759979)
            ·
              refine ⟨28489271936058490253639969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18992847957372326835759979 28489271936058490253639969)
              ·
                refine ⟨21366953952043867690229977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28489271936058490253639969 21366953952043867690229977)
                ·
                  refine ⟨16025215464032900767672483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21366953952043867690229977 16025215464032900767672483)
                  ·
                    refine ⟨24037823196049351151508725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16025215464032900767672483 24037823196049351151508725)
                    ·
                      refine ⟨2253545924629626670453943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24037823196049351151508725 2253545924629626670453943)
                      ·
                        rfl

theorem cell23_4388765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_4388765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4388765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4388765 prefixEnd_4388765 := by exact prefixLift 4388765
  have htrace : WordTrace (prefixWord ++ tailWord_4388765) baseStart_4388765 baseEnd_4388765 := by
    simpa [prefixWord, tailWord_4388765, baseEnd_4388765] using wordTrace_append hprefix tailTrace_4388765
  have hstable : (prefixWord ++ tailWord_4388765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388765).length < 2 ^ (prefixWord ++ tailWord_4388765).sum := by decide
  have hdescent : baseEnd_4388765 < baseStart_4388765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388768 : List Nat := [2, 1, 1, 4, 1, 1, 1, 3, 9]
def baseStart_4388768 : Nat := 118140960795 + 4388768 * 2 ^ 59
def prefixEnd_4388768 : Nat := 4983230072969 + 3 ^ 40 * 4388768 * 2
def baseEnd_4388768 : Nat := 250394162785732239857381

theorem tailTrace_4388768 : CollatzResearch.WordTrace tailWord_4388768 prefixEnd_4388768 250394162785732239857381 := by
  unfold tailWord_4388768
  simp only [CollatzResearch.WordTrace]
  refine ⟨80035759682125276372715479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106714346242833701830287305 80035759682125276372715479)
  ·
    refine ⟨120053639523187914559073219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80035759682125276372715479 120053639523187914559073219)
    ·
      refine ⟨180080459284781871838609829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120053639523187914559073219 180080459284781871838609829)
      ·
        refine ⟨33765086115896600969739343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 180080459284781871838609829 33765086115896600969739343)
        ·
          refine ⟨50647629173844901454609015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33765086115896600969739343 50647629173844901454609015)
          ·
            refine ⟨75971443760767352181913523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50647629173844901454609015 75971443760767352181913523)
            ·
              refine ⟨113957165641151028272870285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75971443760767352181913523 113957165641151028272870285)
              ·
                refine ⟨42733937115431635602326357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113957165641151028272870285 42733937115431635602326357)
                ·
                  refine ⟨250394162785732239857381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 42733937115431635602326357 250394162785732239857381)
                  ·
                    rfl

theorem cell23_4388768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 9].length) (baseStart_4388768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4388768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4388768 prefixEnd_4388768 := by exact prefixLift 4388768
  have htrace : WordTrace (prefixWord ++ tailWord_4388768) baseStart_4388768 baseEnd_4388768 := by
    simpa [prefixWord, tailWord_4388768, baseEnd_4388768] using wordTrace_append hprefix tailTrace_4388768
  have hstable : (prefixWord ++ tailWord_4388768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388768).length < 2 ^ (prefixWord ++ tailWord_4388768).sum := by decide
  have hdescent : baseEnd_4388768 < baseStart_4388768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388812 : List Nat := [2, 2, 1, 4, 1, 3, 1, 1, 2, 3, 3]
def baseStart_4388812 : Nat := 118140960795 + 4388812 * 2 ^ 59
def prefixEnd_4388812 : Nat := 4983230072969 + 3 ^ 40 * 4388812 * 2
def baseEnd_4388812 : Nat := 2253570058220387986566227

theorem tailTrace_4388812 : CollatzResearch.WordTrace tailWord_4388812 prefixEnd_4388812 2253570058220387986566227 := by
  unfold tailWord_4388812
  simp only [CollatzResearch.WordTrace]
  refine ⟨80036562088045574130016345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106715416117394098840021793 80036562088045574130016345)
  ·
    refine ⟨60027421566034180597512259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80036562088045574130016345 60027421566034180597512259)
    ·
      refine ⟨90041132349051270896268389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60027421566034180597512259 90041132349051270896268389)
      ·
        refine ⟨16882712315447113293050323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90041132349051270896268389 16882712315447113293050323)
        ·
          refine ⟨25324068473170669939575485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16882712315447113293050323 25324068473170669939575485)
          ·
            refine ⟨9496525677439001227340807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25324068473170669939575485 9496525677439001227340807)
            ·
              refine ⟨14244788516158501841011211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9496525677439001227340807 14244788516158501841011211)
              ·
                refine ⟨21367182774237752761516817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14244788516158501841011211 21367182774237752761516817)
                ·
                  refine ⟨16025387080678314571137613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21367182774237752761516817 16025387080678314571137613)
                  ·
                    refine ⟨6009520155254367964176605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16025387080678314571137613 6009520155254367964176605)
                    ·
                      refine ⟨2253570058220387986566227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6009520155254367964176605 2253570058220387986566227)
                      ·
                        rfl

theorem cell23_4388812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_4388812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4388812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4388812 prefixEnd_4388812 := by exact prefixLift 4388812
  have htrace : WordTrace (prefixWord ++ tailWord_4388812) baseStart_4388812 baseEnd_4388812 := by
    simpa [prefixWord, tailWord_4388812, baseEnd_4388812] using wordTrace_append hprefix tailTrace_4388812
  have hstable : (prefixWord ++ tailWord_4388812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388812).length < 2 ^ (prefixWord ++ tailWord_4388812).sum := by decide
  have hdescent : baseEnd_4388812 < baseStart_4388812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388865 : List Nat := [1, 2, 4, 1, 2, 1, 1, 2, 2, 1, 6]
def baseStart_4388865 : Nat := 118140960795 + 4388865 * 2 ^ 59
def prefixEnd_4388865 : Nat := 4983230072969 + 3 ^ 40 * 4388865 * 2
def baseEnd_4388865 : Nat := 2253597272695076279203483

theorem tailTrace_4388865 : CollatzResearch.WordTrace tailWord_4388865 prefixEnd_4388865 2253597272695076279203483 := by
  unfold tailWord_4388865
  simp only [CollatzResearch.WordTrace]
  refine ⟨160075057244899138311712049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106716704829932758874474699 160075057244899138311712049)
  ·
    refine ⟨120056292933674353733784037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160075057244899138311712049 120056292933674353733784037)
    ·
      refine ⟨22510554925063941325084507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120056292933674353733784037 22510554925063941325084507)
      ·
        refine ⟨33765832387595911987626761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22510554925063941325084507 33765832387595911987626761)
        ·
          refine ⟨25324374290696933990720071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33765832387595911987626761 25324374290696933990720071)
          ·
            refine ⟨37986561436045400986080107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25324374290696933990720071 37986561436045400986080107)
            ·
              refine ⟨56979842154068101479120161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37986561436045400986080107 56979842154068101479120161)
              ·
                refine ⟨42734881615551076109340121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56979842154068101479120161 42734881615551076109340121)
                ·
                  refine ⟨32051161211663307082005091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42734881615551076109340121 32051161211663307082005091)
                  ·
                    refine ⟨48076741817494960623007637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32051161211663307082005091 48076741817494960623007637)
                    ·
                      refine ⟨2253597272695076279203483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48076741817494960623007637 2253597272695076279203483)
                      ·
                        rfl

theorem cell23_4388865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_4388865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4388865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4388865 prefixEnd_4388865 := by exact prefixLift 4388865
  have htrace : WordTrace (prefixWord ++ tailWord_4388865) baseStart_4388865 baseEnd_4388865 := by
    simpa [prefixWord, tailWord_4388865, baseEnd_4388865] using wordTrace_append hprefix tailTrace_4388865
  have hstable : (prefixWord ++ tailWord_4388865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388865).length < 2 ^ (prefixWord ++ tailWord_4388865).sum := by decide
  have hdescent : baseEnd_4388865 < baseStart_4388865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388919 : List Nat := [1, 1, 3, 1, 2, 2, 5, 1, 3, 1, 3]
def baseStart_4388919 : Nat := 118140960795 + 4388919 * 2 ^ 59
def prefixEnd_4388919 : Nat := 4983230072969 + 3 ^ 40 * 4388919 * 2
def baseEnd_4388919 : Nat := 2253625000650419067928235

theorem tailTrace_4388919 : CollatzResearch.WordTrace tailWord_4388919 prefixEnd_4388919 2253625000650419067928235 := by
  unfold tailWord_4388919
  simp only [CollatzResearch.WordTrace]
  refine ⟨160077026786703505534177811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106718017857802337022785207 160077026786703505534177811)
  ·
    refine ⟨240115540180055258301266717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160077026786703505534177811 240115540180055258301266717)
    ·
      refine ⟨90043327567520721862975019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 240115540180055258301266717 90043327567520721862975019)
      ·
        refine ⟨135064991351281082794462529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90043327567520721862975019 135064991351281082794462529)
        ·
          refine ⟨101298743513460812095846897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135064991351281082794462529 101298743513460812095846897)
          ·
            refine ⟨75974057635095609071885173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101298743513460812095846897 75974057635095609071885173)
            ·
              refine ⟨7122567903290213350489235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75974057635095609071885173 7122567903290213350489235)
              ·
                refine ⟨10683851854935320025733853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7122567903290213350489235 10683851854935320025733853)
                ·
                  refine ⟨4006444445600745009650195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10683851854935320025733853 4006444445600745009650195)
                  ·
                    refine ⟨6009666668401117514475293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4006444445600745009650195 6009666668401117514475293)
                    ·
                      refine ⟨2253625000650419067928235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6009666668401117514475293 2253625000650419067928235)
                      ·
                        rfl

theorem cell23_4388919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 3, 1, 3].length) (baseStart_4388919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4388919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4388919 prefixEnd_4388919 := by exact prefixLift 4388919
  have htrace : WordTrace (prefixWord ++ tailWord_4388919) baseStart_4388919 baseEnd_4388919 := by
    simpa [prefixWord, tailWord_4388919, baseEnd_4388919] using wordTrace_append hprefix tailTrace_4388919
  have hstable : (prefixWord ++ tailWord_4388919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388919).length < 2 ^ (prefixWord ++ tailWord_4388919).sum := by decide
  have hdescent : baseEnd_4388919 < baseStart_4388919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388952 : List Nat := [2, 1, 2, 2, 1, 5, 1, 2, 1, 6]
def baseStart_4388952 : Nat := 118140960795 + 4388952 * 2 ^ 59
def prefixEnd_4388952 : Nat := 4983230072969 + 3 ^ 40 * 4388952 * 2
def baseEnd_4388952 : Nat := 751213981837339146271861

theorem tailTrace_4388952 : CollatzResearch.WordTrace tailWord_4388952 prefixEnd_4388952 751213981837339146271861 := by
  unfold tailWord_4388952
  simp only [CollatzResearch.WordTrace]
  refine ⟨80039115197791976085064555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106718820263722634780086073 80039115197791976085064555)
  ·
    refine ⟨120058672796687964127596833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80039115197791976085064555 120058672796687964127596833)
    ·
      refine ⟨90044004597515973095697625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120058672796687964127596833 90044004597515973095697625)
      ·
        refine ⟨67533003448136979821773219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90044004597515973095697625 67533003448136979821773219)
        ·
          refine ⟨101299505172205469732659829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67533003448136979821773219 101299505172205469732659829)
          ·
            refine ⟨9496828609894262787436859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 101299505172205469732659829 9496828609894262787436859)
            ·
              refine ⟨14245242914841394181155289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9496828609894262787436859 14245242914841394181155289)
              ·
                refine ⟨10683932186131045635866467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14245242914841394181155289 10683932186131045635866467)
                ·
                  refine ⟨16025898279196568453799701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10683932186131045635866467 16025898279196568453799701)
                  ·
                    refine ⟨751213981837339146271861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16025898279196568453799701 751213981837339146271861)
                    ·
                      rfl

theorem cell23_4388952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 1, 6].length) (baseStart_4388952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4388952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4388952 prefixEnd_4388952 := by exact prefixLift 4388952
  have htrace : WordTrace (prefixWord ++ tailWord_4388952) baseStart_4388952 baseEnd_4388952 := by
    simpa [prefixWord, tailWord_4388952, baseEnd_4388952] using wordTrace_append hprefix tailTrace_4388952
  have hstable : (prefixWord ++ tailWord_4388952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388952).length < 2 ^ (prefixWord ++ tailWord_4388952).sum := by decide
  have hdescent : baseEnd_4388952 < baseStart_4388952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388956 : List Nat := [2, 2, 4, 1, 1, 3, 3, 1, 1, 5]
def baseStart_4388956 : Nat := 118140960795 + 4388956 * 2 ^ 59
def prefixEnd_4388956 : Nat := 4983230072969 + 3 ^ 40 * 4388956 * 2
def baseEnd_4388956 : Nat := 751214666478211807721855

theorem tailTrace_4388956 : CollatzResearch.WordTrace tailWord_4388956 prefixEnd_4388956 751214666478211807721855 := by
  unfold tailWord_4388956
  simp only [CollatzResearch.WordTrace]
  refine ⟨80039188143784730426637361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106718917525046307235516481 80039188143784730426637361)
  ·
    refine ⟨60029391107838547819978021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80039188143784730426637361 60029391107838547819978021)
    ·
      refine ⟨11255510832719727716245879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60029391107838547819978021 11255510832719727716245879)
      ·
        refine ⟨16883266249079591574368819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11255510832719727716245879 16883266249079591574368819)
        ·
          refine ⟨25324899373619387361553229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16883266249079591574368819 25324899373619387361553229)
          ·
            refine ⟨9496837265107270260582461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25324899373619387361553229 9496837265107270260582461)
            ·
              refine ⟨3561313974415226347718423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9496837265107270260582461 3561313974415226347718423)
              ·
                refine ⟨5341970961622839521577635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3561313974415226347718423 5341970961622839521577635)
                ·
                  refine ⟨8012956442434259282366453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5341970961622839521577635 8012956442434259282366453)
                  ·
                    refine ⟨751214666478211807721855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8012956442434259282366453 751214666478211807721855)
                    ·
                      rfl

theorem cell23_4388956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_4388956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4388956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4388956 prefixEnd_4388956 := by exact prefixLift 4388956
  have htrace : WordTrace (prefixWord ++ tailWord_4388956) baseStart_4388956 baseEnd_4388956 := by
    simpa [prefixWord, tailWord_4388956, baseEnd_4388956] using wordTrace_append hprefix tailTrace_4388956
  have hstable : (prefixWord ++ tailWord_4388956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388956).length < 2 ^ (prefixWord ++ tailWord_4388956).sum := by decide
  have hdescent : baseEnd_4388956 < baseStart_4388956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388959 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 7, 2, 2]
def baseStart_4388959 : Nat := 118140960795 + 4388959 * 2 ^ 59
def prefixEnd_4388959 : Nat := 4983230072969 + 3 ^ 40 * 4388959 * 2
def baseEnd_4388959 : Nat := 2253645539876598911428051

theorem tailTrace_4388959 : CollatzResearch.WordTrace tailWord_4388959 prefixEnd_4388959 2253645539876598911428051 := by
  unfold tailWord_4388959
  simp only [CollatzResearch.WordTrace]
  refine ⟨160078485706558592365633931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106718990471039061577089287 160078485706558592365633931)
  ·
    refine ⟨240117728559837888548450897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160078485706558592365633931 240117728559837888548450897)
    ·
      refine ⟨180088296419878416411338173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240117728559837888548450897 180088296419878416411338173)
      ·
        refine ⟨67533111157454406154251815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 180088296419878416411338173 67533111157454406154251815)
        ·
          refine ⟨101299666736181609231377723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67533111157454406154251815 101299666736181609231377723)
          ·
            refine ⟨151949500104272413847066585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101299666736181609231377723 151949500104272413847066585)
            ·
              refine ⟨113962125078204310385299939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151949500104272413847066585 113962125078204310385299939)
              ·
                refine ⟨170943187617306465577949909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113962125078204310385299939 170943187617306465577949909)
                ·
                  refine ⟨4006480959780620286983201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 170943187617306465577949909 4006480959780620286983201)
                  ·
                    refine ⟨3004860719835465215237401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4006480959780620286983201 3004860719835465215237401)
                    ·
                      refine ⟨2253645539876598911428051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3004860719835465215237401 2253645539876598911428051)
                      ·
                        rfl

theorem cell23_4388959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 7, 2, 2].length) (baseStart_4388959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4388959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4388959 prefixEnd_4388959 := by exact prefixLift 4388959
  have htrace : WordTrace (prefixWord ++ tailWord_4388959) baseStart_4388959 baseEnd_4388959 := by
    simpa [prefixWord, tailWord_4388959, baseEnd_4388959] using wordTrace_append hprefix tailTrace_4388959
  have hstable : (prefixWord ++ tailWord_4388959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388959).length < 2 ^ (prefixWord ++ tailWord_4388959).sum := by decide
  have hdescent : baseEnd_4388959 < baseStart_4388959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388965 : List Nat := [1, 3, 1, 3, 2, 13]
def baseStart_4388965 : Nat := 118140960795 + 4388965 * 2 ^ 59
def prefixEnd_4388965 : Nat := 4983230072969 + 3 ^ 40 * 4388965 * 2
def baseEnd_4388965 : Nat := 9274274159508336987461

theorem tailTrace_4388965 : CollatzResearch.WordTrace tailWord_4388965 prefixEnd_4388965 9274274159508336987461 := by
  unfold tailWord_4388965
  simp only [CollatzResearch.WordTrace]
  refine ⟨160078704544536855390352349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106719136363024570260234899 160078704544536855390352349)
  ·
    refine ⟨60029514204201320771382131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160078704544536855390352349 60029514204201320771382131)
    ·
      refine ⟨90044271306301981157073197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60029514204201320771382131 90044271306301981157073197)
      ·
        refine ⟨33766601739863242933902449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90044271306301981157073197 33766601739863242933902449)
        ·
          refine ⟨25324951304897432200426837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33766601739863242933902449 25324951304897432200426837)
          ·
            refine ⟨9274274159508336987461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 25324951304897432200426837 9274274159508336987461)
            ·
              rfl

theorem cell23_4388965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 13].length) (baseStart_4388965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4388965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4388965 prefixEnd_4388965 := by exact prefixLift 4388965
  have htrace : WordTrace (prefixWord ++ tailWord_4388965) baseStart_4388965 baseEnd_4388965 := by
    simpa [prefixWord, tailWord_4388965, baseEnd_4388965] using wordTrace_append hprefix tailTrace_4388965
  have hstable : (prefixWord ++ tailWord_4388965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388965).length < 2 ^ (prefixWord ++ tailWord_4388965).sum := by decide
  have hdescent : baseEnd_4388965 < baseStart_4388965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388969 : List Nat := [1, 2, 1, 1, 1, 5, 4, 2, 2, 4]
def baseStart_4388969 : Nat := 118140960795 + 4388969 * 2 ^ 59
def prefixEnd_4388969 : Nat := 4983230072969 + 3 ^ 40 * 4388969 * 2
def baseEnd_4388969 : Nat := 751216891561047957434335

theorem tailTrace_4388969 : CollatzResearch.WordTrace tailWord_4388969 prefixEnd_4388969 751216891561047957434335 := by
  unfold tailWord_4388969
  simp only [CollatzResearch.WordTrace]
  refine ⟨160078850436522364073497961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106719233624348242715665307 160078850436522364073497961)
  ·
    refine ⟨120059137827391773055123471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160078850436522364073497961 120059137827391773055123471)
    ·
      refine ⟨180088706741087659582685207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120059137827391773055123471 180088706741087659582685207)
      ·
        refine ⟨270133060111631489374027811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180088706741087659582685207 270133060111631489374027811)
        ·
          refine ⟨405199590167447234061041717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270133060111631489374027811 405199590167447234061041717)
          ·
            refine ⟨37987461578198178193222661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 405199590167447234061041717 37987461578198178193222661)
            ·
              refine ⟨7122649045912158411229249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37987461578198178193222661 7122649045912158411229249)
              ·
                refine ⟨5341986784434118808421937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7122649045912158411229249 5341986784434118808421937)
                ·
                  refine ⟨4006490088325589106316453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5341986784434118808421937 4006490088325589106316453)
                  ·
                    refine ⟨751216891561047957434335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4006490088325589106316453 751216891561047957434335)
                    ·
                      rfl

theorem cell23_4388969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 2, 4].length) (baseStart_4388969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4388969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4388969 prefixEnd_4388969 := by exact prefixLift 4388969
  have htrace : WordTrace (prefixWord ++ tailWord_4388969) baseStart_4388969 baseEnd_4388969 := by
    simpa [prefixWord, tailWord_4388969, baseEnd_4388969] using wordTrace_append hprefix tailTrace_4388969
  have hstable : (prefixWord ++ tailWord_4388969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388969).length < 2 ^ (prefixWord ++ tailWord_4388969).sum := by decide
  have hdescent : baseEnd_4388969 < baseStart_4388969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388989 : List Nat := [1, 4, 1, 1, 3, 3, 2, 1, 1, 2, 4]
def baseStart_4388989 : Nat := 118140960795 + 4388989 * 2 ^ 59
def prefixEnd_4388989 : Nat := 4983230072969 + 3 ^ 40 * 4388989 * 2
def baseEnd_4388989 : Nat := 2253660944296233794052913

theorem tailTrace_4388989 : CollatzResearch.WordTrace tailWord_4388989 prefixEnd_4388989 2253660944296233794052913 := by
  unfold tailWord_4388989
  simp only [CollatzResearch.WordTrace]
  refine ⟨160079579896449907489226021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106719719930966604992817347 160079579896449907489226021)
  ·
    refine ⟨30014921230584357654229879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160079579896449907489226021 30014921230584357654229879)
    ·
      refine ⟨45022381845876536481344819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30014921230584357654229879 45022381845876536481344819)
      ·
        refine ⟨67533572768814804722017229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45022381845876536481344819 67533572768814804722017229)
        ·
          refine ⟨25325089788305551770756461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67533572768814804722017229 25325089788305551770756461)
          ·
            refine ⟨9496908670614581914033673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25325089788305551770756461 9496908670614581914033673)
            ·
              refine ⟨7122681502960936435525255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9496908670614581914033673 7122681502960936435525255)
              ·
                refine ⟨10684022254441404653287883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7122681502960936435525255 10684022254441404653287883)
                ·
                  refine ⟨16026033381662106979931825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10684022254441404653287883 16026033381662106979931825)
                  ·
                    refine ⟨12019525036246580234948869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16026033381662106979931825 12019525036246580234948869)
                    ·
                      refine ⟨2253660944296233794052913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12019525036246580234948869 2253660944296233794052913)
                      ·
                        rfl

theorem cell23_4388989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 2, 4].length) (baseStart_4388989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4388989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4388989 prefixEnd_4388989 := by exact prefixLift 4388989
  have htrace : WordTrace (prefixWord ++ tailWord_4388989) baseStart_4388989 baseEnd_4388989 := by
    simpa [prefixWord, tailWord_4388989, baseEnd_4388989] using wordTrace_append hprefix tailTrace_4388989
  have hstable : (prefixWord ++ tailWord_4388989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388989).length < 2 ^ (prefixWord ++ tailWord_4388989).sum := by decide
  have hdescent : baseEnd_4388989 < baseStart_4388989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4388993 : List Nat := [1, 2, 4, 2, 3, 1, 1, 2, 3, 2, 2]
def baseStart_4388993 : Nat := 118140960795 + 4388993 * 2 ^ 59
def prefixEnd_4388993 : Nat := 4983230072969 + 3 ^ 40 * 4388993 * 2
def baseEnd_4388993 : Nat := 2253662998218851778402895

theorem tailTrace_4388993 : CollatzResearch.WordTrace tailWord_4388993 prefixEnd_4388993 2253662998218851778402895 := by
  unfold tailWord_4388993
  simp only [CollatzResearch.WordTrace]
  refine ⟨160079725788435416172371633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106719817192290277448247755 160079725788435416172371633)
  ·
    refine ⟨120059794341326562129278725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160079725788435416172371633 120059794341326562129278725)
    ·
      refine ⟨22511211438998730399239761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120059794341326562129278725 22511211438998730399239761)
      ·
        refine ⟨16883408579249047799429821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22511211438998730399239761 16883408579249047799429821)
        ·
          refine ⟨6331278217218392924786183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16883408579249047799429821 6331278217218392924786183)
          ·
            refine ⟨9496917325827589387179275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6331278217218392924786183 9496917325827589387179275)
            ·
              refine ⟨14245375988741384080768913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9496917325827589387179275 14245375988741384080768913)
              ·
                refine ⟨10684031991556038060576685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14245375988741384080768913 10684031991556038060576685)
                ·
                  refine ⟨4006511996833514272716257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10684031991556038060576685 4006511996833514272716257)
                  ·
                    refine ⟨3004883997625135704537193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4006511996833514272716257 3004883997625135704537193)
                    ·
                      refine ⟨2253662998218851778402895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3004883997625135704537193 2253662998218851778402895)
                      ·
                        rfl

theorem cell23_4388993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_4388993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4388993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4388993 prefixEnd_4388993 := by exact prefixLift 4388993
  have htrace : WordTrace (prefixWord ++ tailWord_4388993) baseStart_4388993 baseEnd_4388993 := by
    simpa [prefixWord, tailWord_4388993, baseEnd_4388993] using wordTrace_append hprefix tailTrace_4388993
  have hstable : (prefixWord ++ tailWord_4388993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4388993).length < 2 ^ (prefixWord ++ tailWord_4388993).sum := by decide
  have hdescent : baseEnd_4388993 < baseStart_4388993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4388993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389010 : List Nat := [3, 2, 3, 1, 1, 1, 4, 3, 1, 2, 2]
def baseStart_4389010 : Nat := 118140960795 + 4389010 * 2 ^ 59
def prefixEnd_4389010 : Nat := 4983230072969 + 3 ^ 40 * 4389010 * 2
def baseEnd_4389010 : Nat := 2253671727389978211890317

theorem tailTrace_4389010 : CollatzResearch.WordTrace tailWord_4389010 prefixEnd_4389010 2253671727389978211890317 := by
  unfold tailWord_4389010
  simp only [CollatzResearch.WordTrace]
  refine ⟨40020086457343457018935121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106720230552915885383826989 40020086457343457018935121)
  ·
    refine ⟨30015064843007592764201341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40020086457343457018935121 30015064843007592764201341)
    ·
      refine ⟨11255649316127847286575503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30015064843007592764201341 11255649316127847286575503)
      ·
        refine ⟨16883473974191770929863255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11255649316127847286575503 16883473974191770929863255)
        ·
          refine ⟨25325210961287656394794883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16883473974191770929863255 25325210961287656394794883)
          ·
            refine ⟨37987816441931484592192325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25325210961287656394794883 37987816441931484592192325)
            ·
              refine ⟨7122715582862153361036061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37987816441931484592192325 7122715582862153361036061)
              ·
                refine ⟨2671018343573307510388523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7122715582862153361036061 2671018343573307510388523)
                ·
                  refine ⟨4006527515359961265582785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2671018343573307510388523 4006527515359961265582785)
                  ·
                    refine ⟨3004895636519970949187089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4006527515359961265582785 3004895636519970949187089)
                    ·
                      refine ⟨2253671727389978211890317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3004895636519970949187089 2253671727389978211890317)
                      ·
                        rfl

theorem cell23_4389010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_4389010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389010 prefixEnd_4389010 := by exact prefixLift 4389010
  have htrace : WordTrace (prefixWord ++ tailWord_4389010) baseStart_4389010 baseEnd_4389010 := by
    simpa [prefixWord, tailWord_4389010, baseEnd_4389010] using wordTrace_append hprefix tailTrace_4389010
  have hstable : (prefixWord ++ tailWord_4389010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389010).length < 2 ^ (prefixWord ++ tailWord_4389010).sum := by decide
  have hdescent : baseEnd_4389010 < baseStart_4389010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389042 : List Nat := [3, 2, 1, 1, 1, 3, 1, 3, 2, 6]
def baseStart_4389042 : Nat := 118140960795 + 4389042 * 2 ^ 59
def prefixEnd_4389042 : Nat := 4983230072969 + 3 ^ 40 * 4389042 * 2
def baseEnd_4389042 : Nat := 751229386256974028896723

theorem tailTrace_4389042 : CollatzResearch.WordTrace tailWord_4389042 prefixEnd_4389042 751229386256974028896723 := by
  unfold tailWord_4389042
  simp only [CollatzResearch.WordTrace]
  refine ⟨40020378241314474385226345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106721008643505265027270253 40020378241314474385226345)
  ·
    refine ⟨30015283680985855788919759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40020378241314474385226345 30015283680985855788919759)
    ·
      refine ⟨45022925521478783683379639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30015283680985855788919759 45022925521478783683379639)
      ·
        refine ⟨67534388282218175525069459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45022925521478783683379639 67534388282218175525069459)
        ·
          refine ⟨101301582423327263287604189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67534388282218175525069459 101301582423327263287604189)
          ·
            refine ⟨37988093408747723732851571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101301582423327263287604189 37988093408747723732851571)
            ·
              refine ⟨56982140113121585599277357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37988093408747723732851571 56982140113121585599277357)
              ·
                refine ⟨21368302542420594599729009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56982140113121585599277357 21368302542420594599729009)
                ·
                  refine ⟨16026226906815445949796757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21368302542420594599729009 16026226906815445949796757)
                  ·
                    refine ⟨751229386256974028896723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16026226906815445949796757 751229386256974028896723)
                    ·
                      rfl

theorem cell23_4389042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_4389042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389042 prefixEnd_4389042 := by exact prefixLift 4389042
  have htrace : WordTrace (prefixWord ++ tailWord_4389042) baseStart_4389042 baseEnd_4389042 := by
    simpa [prefixWord, tailWord_4389042, baseEnd_4389042] using wordTrace_append hprefix tailTrace_4389042
  have hstable : (prefixWord ++ tailWord_4389042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389042).length < 2 ^ (prefixWord ++ tailWord_4389042).sum := by decide
  have hdescent : baseEnd_4389042 < baseStart_4389042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389066 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 6, 2, 2]
def baseStart_4389066 : Nat := 118140960795 + 4389066 * 2 ^ 59
def prefixEnd_4389066 : Nat := 4983230072969 + 3 ^ 40 * 4389066 * 2
def baseEnd_4389066 : Nat := 2253700482306629992790059

theorem tailTrace_4389066 : CollatzResearch.WordTrace tailWord_4389066 prefixEnd_4389066 2253700482306629992790059 := by
  unfold tailWord_4389066
  simp only [CollatzResearch.WordTrace]
  refine ⟨40020597079292737409944763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106721592211447299759852701 40020597079292737409944763)
  ·
    refine ⟨60030895618939106114917145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40020597079292737409944763 60030895618939106114917145)
    ·
      refine ⟨45023171714204329586187859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60030895618939106114917145 45023171714204329586187859)
      ·
        refine ⟨67534757571306494379281789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45023171714204329586187859 67534757571306494379281789)
        ·
          refine ⟨25325534089239935392230671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67534757571306494379281789 25325534089239935392230671)
          ·
            refine ⟨37988301133859903088346007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25325534089239935392230671 37988301133859903088346007)
            ·
              refine ⟨56982451700789854632519011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37988301133859903088346007 56982451700789854632519011)
              ·
                refine ⟨85473677551184781948778517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56982451700789854632519011 85473677551184781948778517)
                ·
                  refine ⟨4006578635211786653848993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 85473677551184781948778517 4006578635211786653848993)
                  ·
                    refine ⟨3004933976408839990386745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4006578635211786653848993 3004933976408839990386745)
                    ·
                      refine ⟨2253700482306629992790059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3004933976408839990386745 2253700482306629992790059)
                      ·
                        rfl

theorem cell23_4389066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 6, 2, 2].length) (baseStart_4389066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389066 prefixEnd_4389066 := by exact prefixLift 4389066
  have htrace : WordTrace (prefixWord ++ tailWord_4389066) baseStart_4389066 baseEnd_4389066 := by
    simpa [prefixWord, tailWord_4389066, baseEnd_4389066] using wordTrace_append hprefix tailTrace_4389066
  have hstable : (prefixWord ++ tailWord_4389066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389066).length < 2 ^ (prefixWord ++ tailWord_4389066).sum := by decide
  have hdescent : baseEnd_4389066 < baseStart_4389066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389119 : List Nat := [1, 1, 2, 2, 1, 4, 4, 1, 2, 5]
def baseStart_4389119 : Nat := 118140960795 + 4389119 * 2 ^ 59
def prefixEnd_4389119 : Nat := 4983230072969 + 3 ^ 40 * 4389119 * 2
def baseEnd_4389119 : Nat := 751242565593772761809105

theorem tailTrace_4389119 : CollatzResearch.WordTrace tailWord_4389119 prefixEnd_4389119 751242565593772761809105 := by
  unfold tailWord_4389119
  simp only [CollatzResearch.WordTrace]
  refine ⟨160084321385978939691458411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106722880923985959794305607 160084321385978939691458411)
  ·
    refine ⟨240126482078968409537187617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160084321385978939691458411 240126482078968409537187617)
    ·
      refine ⟨180094861559226307152890713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240126482078968409537187617 180094861559226307152890713)
      ·
        refine ⟨135071146169419730364668035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180094861559226307152890713 135071146169419730364668035)
        ·
          refine ⟨202606719254129595547002053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135071146169419730364668035 202606719254129595547002053)
          ·
            refine ⟨37988759860149299165062885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 202606719254129595547002053 37988759860149299165062885)
            ·
              refine ⟨7122892473777993593449291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37988759860149299165062885 7122892473777993593449291)
              ·
                refine ⟨10684338710666990390173937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7122892473777993593449291 10684338710666990390173937)
                ·
                  refine ⟨8013254033000242792630453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10684338710666990390173937 8013254033000242792630453)
                  ·
                    refine ⟨751242565593772761809105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8013254033000242792630453 751242565593772761809105)
                    ·
                      rfl

theorem cell23_4389119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 5].length) (baseStart_4389119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389119 prefixEnd_4389119 := by exact prefixLift 4389119
  have htrace : WordTrace (prefixWord ++ tailWord_4389119) baseStart_4389119 baseEnd_4389119 := by
    simpa [prefixWord, tailWord_4389119, baseEnd_4389119] using wordTrace_append hprefix tailTrace_4389119
  have hstable : (prefixWord ++ tailWord_4389119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389119).length < 2 ^ (prefixWord ++ tailWord_4389119).sum := by decide
  have hdescent : baseEnd_4389119 < baseStart_4389119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389139 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 3, 6, 2]
def baseStart_4389139 : Nat := 118140960795 + 4389139 * 2 ^ 59
def prefixEnd_4389139 : Nat := 4983230072969 + 3 ^ 40 * 4389139 * 2
def baseEnd_4389139 : Nat := 2253737966394408207177223

theorem tailTrace_4389139 : CollatzResearch.WordTrace tailWord_4389139 prefixEnd_4389139 2253737966394408207177223 := by
  unfold tailWord_4389139
  simp only [CollatzResearch.WordTrace]
  refine ⟨160085050845906483107186471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106723367230604322071457647 160085050845906483107186471)
  ·
    refine ⟨240127576268859724660779707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160085050845906483107186471 240127576268859724660779707)
    ·
      refine ⟨360191364403289586991169561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240127576268859724660779707 360191364403289586991169561)
      ·
        refine ⟨270143523302467190243377171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 360191364403289586991169561 270143523302467190243377171)
        ·
          refine ⟨405215284953700785365065757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270143523302467190243377171 405215284953700785365065757)
          ·
            refine ⟨151955731857637794511899659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 405215284953700785365065757 151955731857637794511899659)
            ·
              refine ⟨227933597786456691767849489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151955731857637794511899659 227933597786456691767849489)
              ·
                refine ⟨170950198339842518825887117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 227933597786456691767849489 170950198339842518825887117)
                ·
                  refine ⟨64106324377440944559707669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 170950198339842518825887117 64106324377440944559707669)
                  ·
                    refine ⟨3004983955192544276236297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 64106324377440944559707669 3004983955192544276236297)
                    ·
                      refine ⟨2253737966394408207177223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3004983955192544276236297 2253737966394408207177223)
                      ·
                        rfl

theorem cell23_4389139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 6, 2].length) (baseStart_4389139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389139 prefixEnd_4389139 := by exact prefixLift 4389139
  have htrace : WordTrace (prefixWord ++ tailWord_4389139) baseStart_4389139 baseEnd_4389139 := by
    simpa [prefixWord, tailWord_4389139, baseEnd_4389139] using wordTrace_append hprefix tailTrace_4389139
  have hstable : (prefixWord ++ tailWord_4389139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389139).length < 2 ^ (prefixWord ++ tailWord_4389139).sum := by decide
  have hdescent : baseEnd_4389139 < baseStart_4389139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389156 : List Nat := [2, 3, 1, 3, 1, 2, 1, 1, 1, 6, 2]
def baseStart_4389156 : Nat := 118140960795 + 4389156 * 2 ^ 59
def prefixEnd_4389156 : Nat := 4983230072969 + 3 ^ 40 * 4389156 * 2
def baseEnd_4389156 : Nat := 2253746695565534640664645

theorem tailTrace_4389156 : CollatzResearch.WordTrace tailWord_4389156 prefixEnd_4389156 2253746695565534640664645 := by
  unfold tailWord_4389156
  simp only [CollatzResearch.WordTrace]
  refine ⟨80042835443422447505277661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106723780591229930007036881 80042835443422447505277661)
  ·
    refine ⟨30016063291283417814479123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80042835443422447505277661 30016063291283417814479123)
    ·
      refine ⟨45024094936925126721718685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30016063291283417814479123 45024094936925126721718685)
      ·
        refine ⟨16884035601346922520644507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45024094936925126721718685 16884035601346922520644507)
        ·
          refine ⟨25326053402020383780966761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16884035601346922520644507 25326053402020383780966761)
          ·
            refine ⟨18994540051515287835725071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25326053402020383780966761 18994540051515287835725071)
            ·
              refine ⟨28491810077272931753587607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18994540051515287835725071 28491810077272931753587607)
              ·
                refine ⟨42737715115909397630381411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28491810077272931753587607 42737715115909397630381411)
                ·
                  refine ⟨64106572673864096445572117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42737715115909397630381411 64106572673864096445572117)
                  ·
                    refine ⟨3004995594087379520886193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 64106572673864096445572117 3004995594087379520886193)
                    ·
                      refine ⟨2253746695565534640664645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3004995594087379520886193 2253746695565534640664645)
                      ·
                        rfl

theorem cell23_4389156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_4389156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389156 prefixEnd_4389156 := by exact prefixLift 4389156
  have htrace : WordTrace (prefixWord ++ tailWord_4389156) baseStart_4389156 baseEnd_4389156 := by
    simpa [prefixWord, tailWord_4389156, baseEnd_4389156] using wordTrace_append hprefix tailTrace_4389156
  have hstable : (prefixWord ++ tailWord_4389156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389156).length < 2 ^ (prefixWord ++ tailWord_4389156).sum := by decide
  have hdescent : baseEnd_4389156 < baseStart_4389156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389176 : List Nat := [2, 1, 2, 1, 3, 1, 5, 1, 2, 2, 3]
def baseStart_4389176 : Nat := 118140960795 + 4389176 * 2 ^ 59
def prefixEnd_4389176 : Nat := 4983230072969 + 3 ^ 40 * 4389176 * 2
def baseEnd_4389176 : Nat := 2253756965178624562414553

theorem tailTrace_4389176 : CollatzResearch.WordTrace tailWord_4389176 prefixEnd_4389176 2253756965178624562414553 := by
  unfold tailWord_4389176
  simp only [CollatzResearch.WordTrace]
  refine ⟨80043200173386219213141691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106724266897848292284188921 80043200173386219213141691)
  ·
    refine ⟨120064800260079328819712537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80043200173386219213141691 120064800260079328819712537)
    ·
      refine ⟨90048600195059496614784403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120064800260079328819712537 90048600195059496614784403)
      ·
        refine ⟨135072900292589244922176605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90048600195059496614784403 135072900292589244922176605)
        ·
          refine ⟨50652337609720966845816227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135072900292589244922176605 50652337609720966845816227)
          ·
            refine ⟨75978506414581450268724341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50652337609720966845816227 75978506414581450268724341)
            ·
              refine ⟨7122984976367010962692907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75978506414581450268724341 7122984976367010962692907)
              ·
                refine ⟨10684477464550516444039361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7122984976367010962692907 10684477464550516444039361)
                ·
                  refine ⟨8013358098412887333029521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10684477464550516444039361 8013358098412887333029521)
                  ·
                    refine ⟨6010018573809665499772141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8013358098412887333029521 6010018573809665499772141)
                    ·
                      refine ⟨2253756965178624562414553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6010018573809665499772141 2253756965178624562414553)
                      ·
                        rfl

theorem cell23_4389176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 2, 2, 3].length) (baseStart_4389176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389176 prefixEnd_4389176 := by exact prefixLift 4389176
  have htrace : WordTrace (prefixWord ++ tailWord_4389176) baseStart_4389176 baseEnd_4389176 := by
    simpa [prefixWord, tailWord_4389176, baseEnd_4389176] using wordTrace_append hprefix tailTrace_4389176
  have hstable : (prefixWord ++ tailWord_4389176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389176).length < 2 ^ (prefixWord ++ tailWord_4389176).sum := by decide
  have hdescent : baseEnd_4389176 < baseStart_4389176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389183 : List Nat := [1, 1, 2, 2, 4, 1, 4, 3, 1, 4]
def baseStart_4389183 : Nat := 118140960795 + 4389183 * 2 ^ 59
def prefixEnd_4389183 : Nat := 4983230072969 + 3 ^ 40 * 4389183 * 2
def baseEnd_4389183 : Nat := 751253519847735345009007

theorem tailTrace_4389183 : CollatzResearch.WordTrace tailWord_4389183 prefixEnd_4389183 751253519847735345009007 := by
  unfold tailWord_4389183
  simp only [CollatzResearch.WordTrace]
  refine ⟨160086655657747078621788203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106724437105164719081192135 160086655657747078621788203)
  ·
    refine ⟨240129983486620617932682305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160086655657747078621788203 240129983486620617932682305)
    ·
      refine ⟨180097487614965463449511729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240129983486620617932682305 180097487614965463449511729)
      ·
        refine ⟨135073115711224097587133797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180097487614965463449511729 135073115711224097587133797)
        ·
          refine ⟨25326209195854518297587587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 135073115711224097587133797 25326209195854518297587587)
          ·
            refine ⟨37989313793781777446381381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25326209195854518297587587 37989313793781777446381381)
            ·
              refine ⟨7122996336334083271196509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37989313793781777446381381 7122996336334083271196509)
              ·
                refine ⟨2671123626125281226698691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7122996336334083271196509 2671123626125281226698691)
                ·
                  refine ⟨4006685439187921840048037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2671123626125281226698691 4006685439187921840048037)
                  ·
                    refine ⟨751253519847735345009007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4006685439187921840048037 751253519847735345009007)
                    ·
                      rfl

theorem cell23_4389183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 3, 1, 4].length) (baseStart_4389183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389183 prefixEnd_4389183 := by exact prefixLift 4389183
  have htrace : WordTrace (prefixWord ++ tailWord_4389183) baseStart_4389183 baseEnd_4389183 := by
    simpa [prefixWord, tailWord_4389183, baseEnd_4389183] using wordTrace_append hprefix tailTrace_4389183
  have hstable : (prefixWord ++ tailWord_4389183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389183).length < 2 ^ (prefixWord ++ tailWord_4389183).sum := by decide
  have hdescent : baseEnd_4389183 < baseStart_4389183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389223 : List Nat := [1, 1, 5, 1, 3, 1, 2, 2, 3, 1, 3]
def baseStart_4389223 : Nat := 118140960795 + 4389223 * 2 ^ 59
def prefixEnd_4389223 : Nat := 4983230072969 + 3 ^ 40 * 4389223 * 2
def baseEnd_4389223 : Nat := 2253781098769385878526837

theorem tailTrace_4389223 : CollatzResearch.WordTrace tailWord_4389223 prefixEnd_4389223 2253781098769385878526837 := by
  unfold tailWord_4389223
  simp only [CollatzResearch.WordTrace]
  refine ⟨160088114577602165453244323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106725409718401443635496215 160088114577602165453244323)
  ·
    refine ⟨240132171866403248179866485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160088114577602165453244323 240132171866403248179866485)
    ·
      refine ⟨22512391112475304516862483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 240132171866403248179866485 22512391112475304516862483)
      ·
        refine ⟨33768586668712956775293725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22512391112475304516862483 33768586668712956775293725)
        ·
          refine ⟨12663220000767358790735147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33768586668712956775293725 12663220000767358790735147)
          ·
            refine ⟨18994830001151038186102721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12663220000767358790735147 18994830001151038186102721)
            ·
              refine ⟨14246122500863278639577041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18994830001151038186102721 14246122500863278639577041)
              ·
                refine ⟨10684591875647458979682781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14246122500863278639577041 10684591875647458979682781)
                ·
                  refine ⟨4006721953367797117381043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10684591875647458979682781 4006721953367797117381043)
                  ·
                    refine ⟨6010082930051695676071565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4006721953367797117381043 6010082930051695676071565)
                    ·
                      refine ⟨2253781098769385878526837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6010082930051695676071565 2253781098769385878526837)
                      ·
                        rfl

theorem cell23_4389223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_4389223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389223 prefixEnd_4389223 := by exact prefixLift 4389223
  have htrace : WordTrace (prefixWord ++ tailWord_4389223) baseStart_4389223 baseEnd_4389223 := by
    simpa [prefixWord, tailWord_4389223, baseEnd_4389223] using wordTrace_append hprefix tailTrace_4389223
  have hstable : (prefixWord ++ tailWord_4389223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389223).length < 2 ^ (prefixWord ++ tailWord_4389223).sum := by decide
  have hdescent : baseEnd_4389223 < baseStart_4389223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389256 : List Nat := [2, 1, 3, 3, 1, 1, 1, 3, 4, 4]
def baseStart_4389256 : Nat := 118140960795 + 4389256 * 2 ^ 59
def prefixEnd_4389256 : Nat := 4983230072969 + 3 ^ 40 * 4389256 * 2
def baseEnd_4389256 : Nat := 751266014543661416471395

theorem tailTrace_4389256 : CollatzResearch.WordTrace tailWord_4389256 prefixEnd_4389256 751266014543661416471395 := by
  unfold tailWord_4389256
  simp only [CollatzResearch.WordTrace]
  refine ⟨80044659093241306044597811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106726212124321741392797081 80044659093241306044597811)
  ·
    refine ⟨120066988639861959066896717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80044659093241306044597811 120066988639861959066896717)
    ·
      refine ⟨45025120739948234650086269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120066988639861959066896717 45025120739948234650086269)
      ·
        refine ⟨16884420277480587993782351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45025120739948234650086269 16884420277480587993782351)
        ·
          refine ⟨25326630416220881990673527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16884420277480587993782351 25326630416220881990673527)
          ·
            refine ⟨37989945624331322986010291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25326630416220881990673527 37989945624331322986010291)
            ·
              refine ⟨56984918436496984479015437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37989945624331322986010291 56984918436496984479015437)
              ·
                refine ⟨21369344413686369179630789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56984918436496984479015437 21369344413686369179630789)
                ·
                  refine ⟨4006752077566194221180773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21369344413686369179630789 4006752077566194221180773)
                  ·
                    refine ⟨751266014543661416471395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4006752077566194221180773 751266014543661416471395)
                    ·
                      rfl

theorem cell23_4389256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 4, 4].length) (baseStart_4389256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389256 prefixEnd_4389256 := by exact prefixLift 4389256
  have htrace : WordTrace (prefixWord ++ tailWord_4389256) baseStart_4389256 baseEnd_4389256 := by
    simpa [prefixWord, tailWord_4389256, baseEnd_4389256] using wordTrace_append hprefix tailTrace_4389256
  have hstable : (prefixWord ++ tailWord_4389256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389256).length < 2 ^ (prefixWord ++ tailWord_4389256).sum := by decide
  have hdescent : baseEnd_4389256 < baseStart_4389256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389257 : List Nat := [1, 2, 1, 1, 6, 2, 3, 2, 1, 1, 3]
def baseStart_4389257 : Nat := 118140960795 + 4389257 * 2 ^ 59
def prefixEnd_4389257 : Nat := 4983230072969 + 3 ^ 40 * 4389257 * 2
def baseEnd_4389257 : Nat := 2253798557111638745501681

theorem tailTrace_4389257 : CollatzResearch.WordTrace tailWord_4389257 prefixEnd_4389257 2253798557111638745501681 := by
  unfold tailWord_4389257
  simp only [CollatzResearch.WordTrace]
  refine ⟨160089354659478989259982025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106726236439652659506654683 160089354659478989259982025)
  ·
    refine ⟨120067015994609241944986519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160089354659478989259982025 120067015994609241944986519)
    ·
      refine ⟨180100523991913862917479779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120067015994609241944986519 180100523991913862917479779)
      ·
        refine ⟨270150785987870794376219669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180100523991913862917479779 270150785987870794376219669)
        ·
          refine ⟨12663318093181443486385297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 270150785987870794376219669 12663318093181443486385297)
          ·
            refine ⟨9497488569886082614788973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12663318093181443486385297 9497488569886082614788973)
            ·
              refine ⟨3561558213707280980545865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9497488569886082614788973 3561558213707280980545865)
              ·
                refine ⟨2671168660280460735409399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3561558213707280980545865 2671168660280460735409399)
                ·
                  refine ⟨4006752990420691103114099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2671168660280460735409399 4006752990420691103114099)
                  ·
                    refine ⟨6010129485631036654671149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4006752990420691103114099 6010129485631036654671149)
                    ·
                      refine ⟨2253798557111638745501681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6010129485631036654671149 2253798557111638745501681)
                      ·
                        rfl

theorem cell23_4389257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 3, 2, 1, 1, 3].length) (baseStart_4389257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389257 prefixEnd_4389257 := by exact prefixLift 4389257
  have htrace : WordTrace (prefixWord ++ tailWord_4389257) baseStart_4389257 baseEnd_4389257 := by
    simpa [prefixWord, tailWord_4389257, baseEnd_4389257] using wordTrace_append hprefix tailTrace_4389257
  have hstable : (prefixWord ++ tailWord_4389257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389257).length < 2 ^ (prefixWord ++ tailWord_4389257).sum := by decide
  have hdescent : baseEnd_4389257 < baseStart_4389257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389259 : List Nat := [1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 6]
def baseStart_4389259 : Nat := 118140960795 + 4389259 * 2 ^ 59
def prefixEnd_4389259 : Nat := 4983230072969 + 3 ^ 40 * 4389259 * 2
def baseEnd_4389259 : Nat := 2253799584072947737676671

theorem tailTrace_4389259 : CollatzResearch.WordTrace tailWord_4389259 prefixEnd_4389259 2253799584072947737676671 := by
  unfold tailWord_4389259
  simp only [CollatzResearch.WordTrace]
  refine ⟨160089427605471743601554831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106726285070314495734369887 160089427605471743601554831)
  ·
    refine ⟨240134141408207615402332247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160089427605471743601554831 240134141408207615402332247)
    ·
      refine ⟨360201212112311423103498371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240134141408207615402332247 360201212112311423103498371)
      ·
        refine ⟨540301818168467134655247557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 360201212112311423103498371 540301818168467134655247557)
        ·
          refine ⟨101306590906587587747858917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 540301818168467134655247557 101306590906587587747858917)
          ·
            refine ⟨18994985794985172702723547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101306590906587587747858917 18994985794985172702723547)
            ·
              refine ⟨28492478692477759054085321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18994985794985172702723547 28492478692477759054085321)
              ·
                refine ⟨21369359019358319290563991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28492478692477759054085321 21369359019358319290563991)
                ·
                  refine ⟨32054038529037478935845987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21369359019358319290563991 32054038529037478935845987)
                  ·
                    refine ⟨48081057793556218403768981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32054038529037478935845987 48081057793556218403768981)
                    ·
                      refine ⟨2253799584072947737676671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48081057793556218403768981 2253799584072947737676671)
                      ·
                        rfl

theorem cell23_4389259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 6].length) (baseStart_4389259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389259 prefixEnd_4389259 := by exact prefixLift 4389259
  have htrace : WordTrace (prefixWord ++ tailWord_4389259) baseStart_4389259 baseEnd_4389259 := by
    simpa [prefixWord, tailWord_4389259, baseEnd_4389259] using wordTrace_append hprefix tailTrace_4389259
  have hstable : (prefixWord ++ tailWord_4389259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389259).length < 2 ^ (prefixWord ++ tailWord_4389259).sum := by decide
  have hdescent : baseEnd_4389259 < baseStart_4389259 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389283 : List Nat := [1, 1, 1, 4, 1, 4, 3, 2, 1, 2, 3]
def baseStart_4389283 : Nat := 118140960795 + 4389283 * 2 ^ 59
def prefixEnd_4389283 : Nat := 4983230072969 + 3 ^ 40 * 4389283 * 2
def baseEnd_4389283 : Nat := 2253811907608655643776561

theorem tailTrace_4389283 : CollatzResearch.WordTrace tailWord_4389283 prefixEnd_4389283 2253811907608655643776561 := by
  unfold tailWord_4389283
  simp only [CollatzResearch.WordTrace]
  refine ⟨160090302957384795700428503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106726868638256530466952335 160090302957384795700428503)
  ·
    refine ⟨240135454436077193550642755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160090302957384795700428503 240135454436077193550642755)
    ·
      refine ⟨360203181654115790325964133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240135454436077193550642755 360203181654115790325964133)
      ·
        refine ⟨67538096560146710686118275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 360203181654115790325964133 67538096560146710686118275)
        ·
          refine ⟨101307144840220066029177413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67538096560146710686118275 101307144840220066029177413)
          ·
            refine ⟨18995089657541262380470765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101307144840220066029177413 18995089657541262380470765)
            ·
              refine ⟨7123158621577973392676537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18995089657541262380470765 7123158621577973392676537)
              ·
                refine ⟨5342368966183480044507403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7123158621577973392676537 5342368966183480044507403)
                ·
                  refine ⟨8013553449275220066761105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5342368966183480044507403 8013553449275220066761105)
                  ·
                    refine ⟨6010165086956415050070829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8013553449275220066761105 6010165086956415050070829)
                    ·
                      refine ⟨2253811907608655643776561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6010165086956415050070829 2253811907608655643776561)
                      ·
                        rfl

theorem cell23_4389283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 2, 3].length) (baseStart_4389283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389283 prefixEnd_4389283 := by exact prefixLift 4389283
  have htrace : WordTrace (prefixWord ++ tailWord_4389283) baseStart_4389283 baseEnd_4389283 := by
    simpa [prefixWord, tailWord_4389283, baseEnd_4389283] using wordTrace_append hprefix tailTrace_4389283
  have hstable : (prefixWord ++ tailWord_4389283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389283).length < 2 ^ (prefixWord ++ tailWord_4389283).sum := by decide
  have hdescent : baseEnd_4389283 < baseStart_4389283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389357 : List Nat := [1, 5, 1, 3, 1, 2, 1, 3, 1, 3, 2]
def baseStart_4389357 : Nat := 118140960795 + 4389357 * 2 ^ 59
def prefixEnd_4389357 : Nat := 4983230072969 + 3 ^ 40 * 4389357 * 2
def baseEnd_4389357 : Nat := 2253849905177088354251221

theorem tailTrace_4389357 : CollatzResearch.WordTrace tailWord_4389357 prefixEnd_4389357 2253849905177088354251221 := by
  unfold tailWord_4389357
  simp only [CollatzResearch.WordTrace]
  refine ⟨160093001959116706338622325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106728667972744470892414883 160093001959116706338622325)
  ·
    refine ⟨15008718933667191219245843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 160093001959116706338622325 15008718933667191219245843)
    ·
      refine ⟨22513078400500786828868765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15008718933667191219245843 22513078400500786828868765)
      ·
        refine ⟨8442404400187795060825787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22513078400500786828868765 8442404400187795060825787)
        ·
          refine ⟨12663606600281692591238681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8442404400187795060825787 12663606600281692591238681)
          ·
            refine ⟨9497704950211269443429011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12663606600281692591238681 9497704950211269443429011)
            ·
              refine ⟨14246557425316904165143517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9497704950211269443429011 14246557425316904165143517)
              ·
                refine ⟨5342459034493839061928819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14246557425316904165143517 5342459034493839061928819)
                ·
                  refine ⟨8013688551740758592893229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5342459034493839061928819 8013688551740758592893229)
                  ·
                    refine ⟨3005133206902784472334961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8013688551740758592893229 3005133206902784472334961)
                    ·
                      refine ⟨2253849905177088354251221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3005133206902784472334961 2253849905177088354251221)
                      ·
                        rfl

theorem cell23_4389357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_4389357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389357 prefixEnd_4389357 := by exact prefixLift 4389357
  have htrace : WordTrace (prefixWord ++ tailWord_4389357) baseStart_4389357 baseEnd_4389357 := by
    simpa [prefixWord, tailWord_4389357, baseEnd_4389357] using wordTrace_append hprefix tailTrace_4389357
  have hstable : (prefixWord ++ tailWord_4389357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389357).length < 2 ^ (prefixWord ++ tailWord_4389357).sum := by decide
  have hdescent : baseEnd_4389357 < baseStart_4389357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389359 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 11]
def baseStart_4389359 : Nat := 118140960795 + 4389359 * 2 ^ 59
def prefixEnd_4389359 : Nat := 4983230072969 + 3 ^ 40 * 4389359 * 2
def baseEnd_4389359 : Nat := 250427881348710816269579

theorem tailTrace_4389359 : CollatzResearch.WordTrace tailWord_4389359 prefixEnd_4389359 250427881348710816269579 := by
  unfold tailWord_4389359
  simp only [CollatzResearch.WordTrace]
  refine ⟨160093074905109460680195131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106728716603406307120130087 160093074905109460680195131)
  ·
    refine ⟨240139612357664191020292697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160093074905109460680195131 240139612357664191020292697)
    ·
      refine ⟨180104709268248143265219523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240139612357664191020292697 180104709268248143265219523)
      ·
        refine ⟨270157063902372214897829285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180104709268248143265219523 270157063902372214897829285)
        ·
          refine ⟨50654449481694790293342991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 270157063902372214897829285 50654449481694790293342991)
          ·
            refine ⟨75981674222542185440014487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50654449481694790293342991 75981674222542185440014487)
            ·
              refine ⟨113972511333813278160021731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75981674222542185440014487 113972511333813278160021731)
              ·
                refine ⟨170958767000719917240032597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113972511333813278160021731 170958767000719917240032597)
                ·
                  refine ⟨250427881348710816269579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 170958767000719917240032597 250427881348710816269579)
                  ·
                    rfl

theorem cell23_4389359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 11].length) (baseStart_4389359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389359 prefixEnd_4389359 := by exact prefixLift 4389359
  have htrace : WordTrace (prefixWord ++ tailWord_4389359) baseStart_4389359 baseEnd_4389359 := by
    simpa [prefixWord, tailWord_4389359, baseEnd_4389359] using wordTrace_append hprefix tailTrace_4389359
  have hstable : (prefixWord ++ tailWord_4389359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389359).length < 2 ^ (prefixWord ++ tailWord_4389359).sum := by decide
  have hdescent : baseEnd_4389359 < baseStart_4389359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389370 : List Nat := [3, 1, 1, 1, 1, 2, 2, 6, 2, 2, 2]
def baseStart_4389370 : Nat := 118140960795 + 4389370 * 2 ^ 59
def prefixEnd_4389370 : Nat := 4983230072969 + 3 ^ 40 * 4389370 * 2
def baseEnd_4389370 : Nat := 2253856580425596803388661

theorem tailTrace_4389370 : CollatzResearch.WordTrace tailWord_4389370 prefixEnd_4389370 2253856580425596803388661 := by
  unfold tailWord_4389370
  simp only [CollatzResearch.WordTrace]
  refine ⟨40023369027017402389711391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106728984072046406372563709 40023369027017402389711391)
  ·
    refine ⟨60035053540526103584567087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40023369027017402389711391 60035053540526103584567087)
    ·
      refine ⟨90052580310789155376850631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60035053540526103584567087 90052580310789155376850631)
      ·
        refine ⟨135078870466183733065275947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90052580310789155376850631 135078870466183733065275947)
        ·
          refine ⟨202618305699275599597913921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135078870466183733065275947 202618305699275599597913921)
          ·
            refine ⟨151963729274456699698435441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202618305699275599597913921 151963729274456699698435441)
            ·
              refine ⟨113972796955842524773826581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151963729274456699698435441 113972796955842524773826581)
              ·
                refine ⟨5342474857305118348773121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 113972796955842524773826581 5342474857305118348773121)
                ·
                  refine ⟨4006856142978838761579841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5342474857305118348773121 4006856142978838761579841)
                  ·
                    refine ⟨3005142107234129071184881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4006856142978838761579841 3005142107234129071184881)
                    ·
                      refine ⟨2253856580425596803388661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3005142107234129071184881 2253856580425596803388661)
                      ·
                        rfl

theorem cell23_4389370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 6, 2, 2, 2].length) (baseStart_4389370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389370 prefixEnd_4389370 := by exact prefixLift 4389370
  have htrace : WordTrace (prefixWord ++ tailWord_4389370) baseStart_4389370 baseEnd_4389370 := by
    simpa [prefixWord, tailWord_4389370, baseEnd_4389370] using wordTrace_append hprefix tailTrace_4389370
  have hstable : (prefixWord ++ tailWord_4389370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389370).length < 2 ^ (prefixWord ++ tailWord_4389370).sum := by decide
  have hdescent : baseEnd_4389370 < baseStart_4389370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389438 : List Nat := [4, 2, 1, 4, 1, 2, 2, 1, 2, 2, 2]
def baseStart_4389438 : Nat := 118140960795 + 4389438 * 2 ^ 59
def prefixEnd_4389438 : Nat := 4983230072969 + 3 ^ 40 * 4389438 * 2
def baseEnd_4389438 : Nat := 2253891497110102537338349

theorem tailTrace_4389438 : CollatzResearch.WordTrace tailWord_4389438 prefixEnd_4389438 2253891497110102537338349 := by
  unfold tailWord_4389438
  simp only [CollatzResearch.WordTrace]
  refine ⟨20011994533977907146540121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106730637514548838114880645 20011994533977907146540121)
  ·
    refine ⟨15008995900483430359905091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20011994533977907146540121 15008995900483430359905091)
    ·
      refine ⟨22513493850725145539857637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15008995900483430359905091 22513493850725145539857637)
      ·
        refine ⟨4221280097010964788723307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22513493850725145539857637 4221280097010964788723307)
        ·
          refine ⟨6331920145516447183084961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4221280097010964788723307 6331920145516447183084961)
          ·
            refine ⟨4748940109137335387313721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6331920145516447183084961 4748940109137335387313721)
            ·
              refine ⟨3561705081853001540485291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4748940109137335387313721 3561705081853001540485291)
              ·
                refine ⟨5342557622779502310727937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3561705081853001540485291 5342557622779502310727937)
                ·
                  refine ⟨4006918217084626733045953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5342557622779502310727937 4006918217084626733045953)
                  ·
                    refine ⟨3005188662813470049784465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4006918217084626733045953 3005188662813470049784465)
                    ·
                      refine ⟨2253891497110102537338349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3005188662813470049784465 2253891497110102537338349)
                      ·
                        rfl

theorem cell23_4389438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_4389438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389438 prefixEnd_4389438 := by exact prefixLift 4389438
  have htrace : WordTrace (prefixWord ++ tailWord_4389438) baseStart_4389438 baseEnd_4389438 := by
    simpa [prefixWord, tailWord_4389438, baseEnd_4389438] using wordTrace_append hprefix tailTrace_4389438
  have hstable : (prefixWord ++ tailWord_4389438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389438).length < 2 ^ (prefixWord ++ tailWord_4389438).sum := by decide
  have hdescent : baseEnd_4389438 < baseStart_4389438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389443 : List Nat := [1, 1, 1, 3, 1, 2, 1, 5, 2, 4, 2]
def baseStart_4389443 : Nat := 118140960795 + 4389443 * 2 ^ 59
def prefixEnd_4389443 : Nat := 4983230072969 + 3 ^ 40 * 4389443 * 2
def baseEnd_4389443 : Nat := 2253894064513375017775825

theorem tailTrace_4389443 : CollatzResearch.WordTrace tailWord_4389443 prefixEnd_4389443 2253894064513375017775825 := by
  unfold tailWord_4389443
  simp only [CollatzResearch.WordTrace]
  refine ⟨160096138636805143026252983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106730759091203428684168655 160096138636805143026252983)
  ·
    refine ⟨240144207955207714539379475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160096138636805143026252983 240144207955207714539379475)
    ·
      refine ⟨360216311932811571809069213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240144207955207714539379475 360216311932811571809069213)
      ·
        refine ⟨135081116974804339428400955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 360216311932811571809069213 135081116974804339428400955)
        ·
          refine ⟨202621675462206509142601433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135081116974804339428400955 202621675462206509142601433)
          ·
            refine ⟨151966256596654881856951075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202621675462206509142601433 151966256596654881856951075)
            ·
              refine ⟨227949384894982322785426613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151966256596654881856951075 227949384894982322785426613)
              ·
                refine ⟨21370254833904592761133745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 227949384894982322785426613 21370254833904592761133745)
                ·
                  refine ⟨16027691125428444570850309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21370254833904592761133745 16027691125428444570850309)
                  ·
                    refine ⟨3005192086017833357034433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16027691125428444570850309 3005192086017833357034433)
                    ·
                      refine ⟨2253894064513375017775825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3005192086017833357034433 2253894064513375017775825)
                      ·
                        rfl

theorem cell23_4389443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 4, 2].length) (baseStart_4389443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389443 prefixEnd_4389443 := by exact prefixLift 4389443
  have htrace : WordTrace (prefixWord ++ tailWord_4389443) baseStart_4389443 baseEnd_4389443 := by
    simpa [prefixWord, tailWord_4389443, baseEnd_4389443] using wordTrace_append hprefix tailTrace_4389443
  have hstable : (prefixWord ++ tailWord_4389443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389443).length < 2 ^ (prefixWord ++ tailWord_4389443).sum := by decide
  have hdescent : baseEnd_4389443 < baseStart_4389443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389460 : List Nat := [2, 4, 1, 1, 1, 4, 2, 1, 2, 1, 4]
def baseStart_4389460 : Nat := 118140960795 + 4389460 * 2 ^ 59
def prefixEnd_4389460 : Nat := 4983230072969 + 3 ^ 40 * 4389460 * 2
def baseEnd_4389460 : Nat := 2253902793684501451263247

theorem tailTrace_4389460 : CollatzResearch.WordTrace tailWord_4389460 prefixEnd_4389460 2253902793684501451263247 := by
  unfold tailWord_4389460
  simp only [CollatzResearch.WordTrace]
  refine ⟨80048379338871777464810917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106731172451829036619747889 80048379338871777464810917)
  ·
    refine ⟨15009071126038458274652047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80048379338871777464810917 15009071126038458274652047)
    ·
      refine ⟨22513606689057687411978071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15009071126038458274652047 22513606689057687411978071)
      ·
        refine ⟨33770410033586531117967107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22513606689057687411978071 33770410033586531117967107)
        ·
          refine ⟨50655615050379796676950661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33770410033586531117967107 50655615050379796676950661)
          ·
            refine ⟨9497927821946211876928249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50655615050379796676950661 9497927821946211876928249)
            ·
              refine ⟨7123445866459658907696187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9497927821946211876928249 7123445866459658907696187)
              ·
                refine ⟨10685168799689488361544281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7123445866459658907696187 10685168799689488361544281)
                ·
                  refine ⟨8013876599767116271158211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10685168799689488361544281 8013876599767116271158211)
                  ·
                    refine ⟨12020814899650674406737317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8013876599767116271158211 12020814899650674406737317)
                    ·
                      refine ⟨2253902793684501451263247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12020814899650674406737317 2253902793684501451263247)
                      ·
                        rfl

theorem cell23_4389460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_4389460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389460 prefixEnd_4389460 := by exact prefixLift 4389460
  have htrace : WordTrace (prefixWord ++ tailWord_4389460) baseStart_4389460 baseEnd_4389460 := by
    simpa [prefixWord, tailWord_4389460, baseEnd_4389460] using wordTrace_append hprefix tailTrace_4389460
  have hstable : (prefixWord ++ tailWord_4389460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389460).length < 2 ^ (prefixWord ++ tailWord_4389460).sum := by decide
  have hdescent : baseEnd_4389460 < baseStart_4389460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389487 : List Nat := [1, 1, 2, 1, 3, 2, 6, 2, 1, 4]
def baseStart_4389487 : Nat := 118140960795 + 4389487 * 2 ^ 59
def prefixEnd_4389487 : Nat := 4983230072969 + 3 ^ 40 * 4389487 * 2
def baseEnd_4389487 : Nat := 751305552554057615208541

theorem tailTrace_4389487 : CollatzResearch.WordTrace tailWord_4389487 prefixEnd_4389487 751305552554057615208541 := by
  unfold tailWord_4389487
  simp only [CollatzResearch.WordTrace]
  refine ⟨160097743448645738540854715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106731828965763825693903143 160097743448645738540854715)
  ·
    refine ⟨240146615172968607811282073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160097743448645738540854715 240146615172968607811282073)
    ·
      refine ⟨180109961379726455858461555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240146615172968607811282073 180109961379726455858461555)
      ·
        refine ⟨270164942069589683787692333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180109961379726455858461555 270164942069589683787692333)
        ·
          refine ⟨101311853276096131420384625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 270164942069589683787692333 101311853276096131420384625)
          ·
            refine ⟨75983889957072098565288469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101311853276096131420384625 75983889957072098565288469)
            ·
              refine ⟨3561744841737754620247897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 75983889957072098565288469 3561744841737754620247897)
              ·
                refine ⟨2671308631303315965185923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3561744841737754620247897 2671308631303315965185923)
                ·
                  refine ⟨4006962946954973947778885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2671308631303315965185923 4006962946954973947778885)
                  ·
                    refine ⟨751305552554057615208541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4006962946954973947778885 751305552554057615208541)
                    ·
                      rfl

theorem cell23_4389487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 2, 1, 4].length) (baseStart_4389487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389487 prefixEnd_4389487 := by exact prefixLift 4389487
  have htrace : WordTrace (prefixWord ++ tailWord_4389487) baseStart_4389487 baseEnd_4389487 := by
    simpa [prefixWord, tailWord_4389487, baseEnd_4389487] using wordTrace_append hprefix tailTrace_4389487
  have hstable : (prefixWord ++ tailWord_4389487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389487).length < 2 ^ (prefixWord ++ tailWord_4389487).sum := by decide
  have hdescent : baseEnd_4389487 < baseStart_4389487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389513 : List Nat := [1, 2, 1, 1, 4, 1, 1, 6, 1, 5]
def baseStart_4389513 : Nat := 118140960795 + 4389513 * 2 ^ 59
def prefixEnd_4389513 : Nat := 4983230072969 + 3 ^ 40 * 4389513 * 2
def baseEnd_4389513 : Nat := 751310002719729914633501

theorem tailTrace_4389513 : CollatzResearch.WordTrace tailWord_4389513 prefixEnd_4389513 751310002719729914633501 := by
  unfold tailWord_4389513
  simp only [CollatzResearch.WordTrace]
  refine ⟨160098691746551544981301193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106732461164367696654200795 160098691746551544981301193)
  ·
    refine ⟨120074018809913658735975895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160098691746551544981301193 120074018809913658735975895)
    ·
      refine ⟨180111028214870488103963843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120074018809913658735975895 180111028214870488103963843)
      ·
        refine ⟨270166542322305732155945765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180111028214870488103963843 270166542322305732155945765)
        ·
          refine ⟨50656226685432324779239831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 270166542322305732155945765 50656226685432324779239831)
          ·
            refine ⟨75984340028148487168859747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50656226685432324779239831 75984340028148487168859747)
            ·
              refine ⟨113976510042222730753289621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75984340028148487168859747 113976510042222730753289621)
              ·
                refine ⟨5342648908229190504060451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 113976510042222730753289621 5342648908229190504060451)
                ·
                  refine ⟨8013973362343785756090677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5342648908229190504060451 8013973362343785756090677)
                  ·
                    refine ⟨751310002719729914633501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8013973362343785756090677 751310002719729914633501)
                    ·
                      rfl

theorem cell23_4389513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 5].length) (baseStart_4389513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389513 prefixEnd_4389513 := by exact prefixLift 4389513
  have htrace : WordTrace (prefixWord ++ tailWord_4389513) baseStart_4389513 baseEnd_4389513 := by
    simpa [prefixWord, tailWord_4389513, baseEnd_4389513] using wordTrace_append hprefix tailTrace_4389513
  have hstable : (prefixWord ++ tailWord_4389513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389513).length < 2 ^ (prefixWord ++ tailWord_4389513).sum := by decide
  have hdescent : baseEnd_4389513 < baseStart_4389513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389514 : List Nat := [3, 1, 2, 3, 4, 1, 1, 1, 2, 2, 3]
def baseStart_4389514 : Nat := 118140960795 + 4389514 * 2 ^ 59
def prefixEnd_4389514 : Nat := 4983230072969 + 3 ^ 40 * 4389514 * 2
def baseEnd_4389514 : Nat := 2253930521639844239987999

theorem tailTrace_4389514 : CollatzResearch.WordTrace tailWord_4389514 prefixEnd_4389514 2253930521639844239987999 := by
  unfold tailWord_4389514
  simp only [CollatzResearch.WordTrace]
  refine ⟨40024682054886980538021899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106732485479698614768058397 40024682054886980538021899)
  ·
    refine ⟨60037023082330470807032849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40024682054886980538021899 60037023082330470807032849)
    ·
      refine ⟨45027767311747853105274637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60037023082330470807032849 45027767311747853105274637)
      ·
        refine ⟨16885412741905444914477989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45027767311747853105274637 16885412741905444914477989)
        ·
          refine ⟨3166014889107270921464623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16885412741905444914477989 3166014889107270921464623)
          ·
            refine ⟨4749022333660906382196935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3166014889107270921464623 4749022333660906382196935)
            ·
              refine ⟨7123533500491359573295403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4749022333660906382196935 7123533500491359573295403)
              ·
                refine ⟨10685300250737039359943105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7123533500491359573295403 10685300250737039359943105)
                ·
                  refine ⟨8013975188052779519957329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10685300250737039359943105 8013975188052779519957329)
                  ·
                    refine ⟨6010481391039584639967997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8013975188052779519957329 6010481391039584639967997)
                    ·
                      refine ⟨2253930521639844239987999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6010481391039584639967997 2253930521639844239987999)
                      ·
                        rfl

theorem cell23_4389514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_4389514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389514 prefixEnd_4389514 := by exact prefixLift 4389514
  have htrace : WordTrace (prefixWord ++ tailWord_4389514) baseStart_4389514 baseEnd_4389514 := by
    simpa [prefixWord, tailWord_4389514, baseEnd_4389514] using wordTrace_append hprefix tailTrace_4389514
  have hstable : (prefixWord ++ tailWord_4389514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389514).length < 2 ^ (prefixWord ++ tailWord_4389514).sum := by decide
  have hdescent : baseEnd_4389514 < baseStart_4389514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389567 : List Nat := [1, 1, 2, 2, 2, 4, 2, 2, 3, 2, 2]
def baseStart_4389567 : Nat := 118140960795 + 4389567 * 2 ^ 59
def prefixEnd_4389567 : Nat := 4983230072969 + 3 ^ 40 * 4389567 * 2
def baseEnd_4389567 : Nat := 2253957736114532532625255

theorem tailTrace_4389567 : CollatzResearch.WordTrace tailWord_4389567 prefixEnd_4389567 2253957736114532532625255 := by
  unfold tailWord_4389567
  simp only [CollatzResearch.WordTrace]
  refine ⟨160100661288355912203766955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106733774192237274802511303 160100661288355912203766955)
  ·
    refine ⟨240150991932533868305650433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160100661288355912203766955 240150991932533868305650433)
    ·
      refine ⟨180113243949400401229237825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240150991932533868305650433 180113243949400401229237825)
      ·
        refine ⟨135084932962050300921928369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180113243949400401229237825 135084932962050300921928369)
        ·
          refine ⟨101313699721537725691446277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135084932962050300921928369 101313699721537725691446277)
          ·
            refine ⟨18996318697788323567146177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101313699721537725691446277 18996318697788323567146177)
            ·
              refine ⟨14247239023341242675359633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18996318697788323567146177 14247239023341242675359633)
              ·
                refine ⟨10685429267505932006519725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14247239023341242675359633 10685429267505932006519725)
                ·
                  refine ⟨4007035975314724502444897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10685429267505932006519725 4007035975314724502444897)
                  ·
                    refine ⟨3005276981486043376833673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4007035975314724502444897 3005276981486043376833673)
                    ·
                      refine ⟨2253957736114532532625255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3005276981486043376833673 2253957736114532532625255)
                      ·
                        rfl

theorem cell23_4389567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 3, 2, 2].length) (baseStart_4389567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389567 prefixEnd_4389567 := by exact prefixLift 4389567
  have htrace : WordTrace (prefixWord ++ tailWord_4389567) baseStart_4389567 baseEnd_4389567 := by
    simpa [prefixWord, tailWord_4389567, baseEnd_4389567] using wordTrace_append hprefix tailTrace_4389567
  have hstable : (prefixWord ++ tailWord_4389567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389567).length < 2 ^ (prefixWord ++ tailWord_4389567).sum := by decide
  have hdescent : baseEnd_4389567 < baseStart_4389567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389610 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 2, 7, 2]
def baseStart_4389610 : Nat := 118140960795 + 4389610 * 2 ^ 59
def prefixEnd_4389610 : Nat := 4983230072969 + 3 ^ 40 * 4389610 * 2
def baseEnd_4389610 : Nat := 2253979815782675864387557

theorem tailTrace_4389610 : CollatzResearch.WordTrace tailWord_4389610 prefixEnd_4389610 2253979815782675864387557 := by
  unfold tailWord_4389610
  simp only [CollatzResearch.WordTrace]
  refine ⟨40025557406800032636895571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106734819751466753698388189 40025557406800032636895571)
  ·
    refine ⟨60038336110200048955343357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40025557406800032636895571 60038336110200048955343357)
    ·
      refine ⟨22514376041325018358253759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60038336110200048955343357 22514376041325018358253759)
      ·
        refine ⟨33771564061987527537380639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22514376041325018358253759 33771564061987527537380639)
        ·
          refine ⟨50657346092981291306070959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33771564061987527537380639 50657346092981291306070959)
          ·
            refine ⟨75986019139471936959106439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50657346092981291306070959 75986019139471936959106439)
            ·
              refine ⟨113979028709207905438659659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75986019139471936959106439 113979028709207905438659659)
              ·
                refine ⟨170968543063811858157989489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113979028709207905438659659 170968543063811858157989489)
                ·
                  refine ⟨128226407297858893618492117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 170968543063811858157989489 128226407297858893618492117)
                  ·
                    refine ⟨3005306421043567819183409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 128226407297858893618492117 3005306421043567819183409)
                    ·
                      refine ⟨2253979815782675864387557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3005306421043567819183409 2253979815782675864387557)
                      ·
                        rfl

theorem cell23_4389610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_4389610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389610 prefixEnd_4389610 := by exact prefixLift 4389610
  have htrace : WordTrace (prefixWord ++ tailWord_4389610) baseStart_4389610 baseEnd_4389610 := by
    simpa [prefixWord, tailWord_4389610, baseEnd_4389610] using wordTrace_append hprefix tailTrace_4389610
  have hstable : (prefixWord ++ tailWord_4389610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389610).length < 2 ^ (prefixWord ++ tailWord_4389610).sum := by decide
  have hdescent : baseEnd_4389610 < baseStart_4389610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389617 : List Nat := [1, 2, 2, 2, 2, 2, 3, 3, 2, 1, 3]
def baseStart_4389617 : Nat := 118140960795 + 4389617 * 2 ^ 59
def prefixEnd_4389617 : Nat := 4983230072969 + 3 ^ 40 * 4389617 * 2
def baseEnd_4389617 : Nat := 2253983410147257337000025

theorem tailTrace_4389617 : CollatzResearch.WordTrace tailWord_4389617 prefixEnd_4389617 2253983410147257337000025 := by
  unfold tailWord_4389617
  simp only [CollatzResearch.WordTrace]
  refine ⟨160102484938174770743087105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106734989958783180495391403 160102484938174770743087105)
  ·
    refine ⟨120076863703631078057315329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160102484938174770743087105 120076863703631078057315329)
    ·
      refine ⟨90057647777723308542986497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120076863703631078057315329 90057647777723308542986497)
      ·
        refine ⟨67543235833292481407239873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90057647777723308542986497 67543235833292481407239873)
        ·
          refine ⟨50657426874969361055429905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67543235833292481407239873 50657426874969361055429905)
          ·
            refine ⟨37993070156227020791572429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50657426874969361055429905 37993070156227020791572429)
            ·
              refine ⟨14247401308585132796839661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37993070156227020791572429 14247401308585132796839661)
              ·
                refine ⟨5342775490719424798814873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14247401308585132796839661 5342775490719424798814873)
                ·
                  refine ⟨4007081618039568599111155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5342775490719424798814873 4007081618039568599111155)
                  ·
                    refine ⟨6010622427059352898666733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4007081618039568599111155 6010622427059352898666733)
                    ·
                      refine ⟨2253983410147257337000025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6010622427059352898666733 2253983410147257337000025)
                      ·
                        rfl

theorem cell23_4389617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 2, 1, 3].length) (baseStart_4389617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389617 prefixEnd_4389617 := by exact prefixLift 4389617
  have htrace : WordTrace (prefixWord ++ tailWord_4389617) baseStart_4389617 baseEnd_4389617 := by
    simpa [prefixWord, tailWord_4389617, baseEnd_4389617] using wordTrace_append hprefix tailTrace_4389617
  have hstable : (prefixWord ++ tailWord_4389617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389617).length < 2 ^ (prefixWord ++ tailWord_4389617).sum := by decide
  have hdescent : baseEnd_4389617 < baseStart_4389617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389621 : List Nat := [1, 3, 6, 1, 1, 1, 1, 1, 3, 2, 3]
def baseStart_4389621 : Nat := 118140960795 + 4389621 * 2 ^ 59
def prefixEnd_4389621 : Nat := 4983230072969 + 3 ^ 40 * 4389621 * 2
def baseEnd_4389621 : Nat := 2253985464069875321350007

theorem tailTrace_4389621 : CollatzResearch.WordTrace tailWord_4389621 prefixEnd_4389621 2253985464069875321350007 := by
  unfold tailWord_4389621
  simp only [CollatzResearch.WordTrace]
  refine ⟨160102630830160279426232717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106735087220106852950821811 160102630830160279426232717)
  ·
    refine ⟨60038486561310104784837269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160102630830160279426232717 60038486561310104784837269)
    ·
      refine ⟨2814304057561411161789247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 60038486561310104784837269 2814304057561411161789247)
      ·
        refine ⟨4221456086342116742683871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2814304057561411161789247 4221456086342116742683871)
        ·
          refine ⟨6332184129513175114025807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4221456086342116742683871 6332184129513175114025807)
          ·
            refine ⟨9498276194269762671038711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6332184129513175114025807 9498276194269762671038711)
            ·
              refine ⟨14247414291404644006558067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9498276194269762671038711 14247414291404644006558067)
              ·
                refine ⟨21371121437106966009837101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14247414291404644006558067 21371121437106966009837101)
                ·
                  refine ⟨8014170538915112253688913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21371121437106966009837101 8014170538915112253688913)
                  ·
                    refine ⟨6010627904186334190266685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8014170538915112253688913 6010627904186334190266685)
                    ·
                      refine ⟨2253985464069875321350007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6010627904186334190266685 2253985464069875321350007)
                      ·
                        rfl

theorem cell23_4389621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_4389621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389621 prefixEnd_4389621 := by exact prefixLift 4389621
  have htrace : WordTrace (prefixWord ++ tailWord_4389621) baseStart_4389621 baseEnd_4389621 := by
    simpa [prefixWord, tailWord_4389621, baseEnd_4389621] using wordTrace_append hprefix tailTrace_4389621
  have hstable : (prefixWord ++ tailWord_4389621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389621).length < 2 ^ (prefixWord ++ tailWord_4389621).sum := by decide
  have hdescent : baseEnd_4389621 < baseStart_4389621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389633 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 4, 6]
def baseStart_4389633 : Nat := 118140960795 + 4389633 * 2 ^ 59
def prefixEnd_4389633 : Nat := 4983230072969 + 3 ^ 40 * 4389633 * 2
def baseEnd_4389633 : Nat := 751330541945909758133317

theorem tailTrace_4389633 : CollatzResearch.WordTrace tailWord_4389633 prefixEnd_4389633 751330541945909758133317 := by
  unfold tailWord_4389633
  simp only [CollatzResearch.WordTrace]
  refine ⟨160103068506116805475669553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106735379004077870317113035 160103068506116805475669553)
  ·
    refine ⟨120077301379587604106752165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160103068506116805475669553 120077301379587604106752165)
    ·
      refine ⟨22514494008672675770016031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120077301379587604106752165 22514494008672675770016031)
      ·
        refine ⟨33771741013009013655024047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22514494008672675770016031 33771741013009013655024047)
        ·
          refine ⟨50657611519513520482536071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33771741013009013655024047 50657611519513520482536071)
          ·
            refine ⟨75986417279270280723804107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50657611519513520482536071 75986417279270280723804107)
            ·
              refine ⟨113979625918905421085706161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75986417279270280723804107 113979625918905421085706161)
              ·
                refine ⟨85484719439179065814279621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113979625918905421085706161 85484719439179065814279621)
                ·
                  refine ⟨16028384894846074840177429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85484719439179065814279621 16028384894846074840177429)
                  ·
                    refine ⟨751330541945909758133317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16028384894846074840177429 751330541945909758133317)
                    ·
                      rfl

theorem cell23_4389633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_4389633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389633 prefixEnd_4389633 := by exact prefixLift 4389633
  have htrace : WordTrace (prefixWord ++ tailWord_4389633) baseStart_4389633 baseEnd_4389633 := by
    simpa [prefixWord, tailWord_4389633, baseEnd_4389633] using wordTrace_append hprefix tailTrace_4389633
  have hstable : (prefixWord ++ tailWord_4389633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389633).length < 2 ^ (prefixWord ++ tailWord_4389633).sum := by decide
  have hdescent : baseEnd_4389633 < baseStart_4389633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389660 : List Nat := [2, 2, 3, 1, 1, 3, 1, 1, 2, 4, 3]
def baseStart_4389660 : Nat := 118140960795 + 4389660 * 2 ^ 59
def prefixEnd_4389660 : Nat := 4983230072969 + 3 ^ 40 * 4389660 * 2
def baseEnd_4389660 : Nat := 2254005489815400668762327

theorem tailTrace_4389660 : CollatzResearch.WordTrace tailWord_4389660 prefixEnd_4389660 2254005489815400668762327 := by
  unfold tailWord_4389660
  simp only [CollatzResearch.WordTrace]
  refine ⟨80052026638509494543451217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106736035518012659391268289 80052026638509494543451217)
  ·
    refine ⟨60039019978882120907588413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80052026638509494543451217 60039019978882120907588413)
    ·
      refine ⟨22514632492080795340345655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60039019978882120907588413 22514632492080795340345655)
      ·
        refine ⟨33771948738121193010518483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22514632492080795340345655 33771948738121193010518483)
        ·
          refine ⟨50657923107181789515777725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33771948738121193010518483 50657923107181789515777725)
          ·
            refine ⟨18996721165193171068416647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50657923107181789515777725 18996721165193171068416647)
            ·
              refine ⟨28495081747789756602624971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18996721165193171068416647 28495081747789756602624971)
              ·
                refine ⟨42742622621684634903937457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28495081747789756602624971 42742622621684634903937457)
                ·
                  refine ⟨32056966966263476177953093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42742622621684634903937457 32056966966263476177953093)
                  ·
                    refine ⟨6010681306174401783366205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32056966966263476177953093 6010681306174401783366205)
                    ·
                      refine ⟨2254005489815400668762327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6010681306174401783366205 2254005489815400668762327)
                      ·
                        rfl

theorem cell23_4389660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_4389660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389660 prefixEnd_4389660 := by exact prefixLift 4389660
  have htrace : WordTrace (prefixWord ++ tailWord_4389660) baseStart_4389660 baseEnd_4389660 := by
    simpa [prefixWord, tailWord_4389660, baseEnd_4389660] using wordTrace_append hprefix tailTrace_4389660
  have hstable : (prefixWord ++ tailWord_4389660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389660).length < 2 ^ (prefixWord ++ tailWord_4389660).sum := by decide
  have hdescent : baseEnd_4389660 < baseStart_4389660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389710 : List Nat := [4, 1, 1, 1, 1, 1, 1, 6, 2, 5]
def baseStart_4389710 : Nat := 118140960795 + 4389710 * 2 ^ 59
def prefixEnd_4389710 : Nat := 4983230072969 + 3 ^ 40 * 4389710 * 2
def baseEnd_4389710 : Nat := 751343721282708491045699

theorem tailTrace_4389710 : CollatzResearch.WordTrace tailWord_4389710 prefixEnd_4389710 751343721282708491045699 := by
  unfold tailWord_4389710
  simp only [CollatzResearch.WordTrace]
  refine ⟨20013234615854730953277823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106737251284558565084148389 20013234615854730953277823)
  ·
    refine ⟨30019851923782096429916735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20013234615854730953277823 30019851923782096429916735)
    ·
      refine ⟨45029777885673144644875103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30019851923782096429916735 45029777885673144644875103)
      ·
        refine ⟨67544666828509716967312655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45029777885673144644875103 67544666828509716967312655)
        ·
          refine ⟨101317000242764575450968983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67544666828509716967312655 101317000242764575450968983)
          ·
            refine ⟨151975500364146863176453475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101317000242764575450968983 151975500364146863176453475)
            ·
              refine ⟨227963250546220294764680213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151975500364146863176453475 227963250546220294764680213)
              ·
                refine ⟨10685777369354076317094385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 227963250546220294764680213 10685777369354076317094385)
                ·
                  refine ⟨8014333027015557237820789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10685777369354076317094385 8014333027015557237820789)
                  ·
                    refine ⟨751343721282708491045699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8014333027015557237820789 751343721282708491045699)
                    ·
                      rfl

theorem cell23_4389710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_4389710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389710 prefixEnd_4389710 := by exact prefixLift 4389710
  have htrace : WordTrace (prefixWord ++ tailWord_4389710) baseStart_4389710 baseEnd_4389710 := by
    simpa [prefixWord, tailWord_4389710, baseEnd_4389710] using wordTrace_append hprefix tailTrace_4389710
  have hstable : (prefixWord ++ tailWord_4389710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389710).length < 2 ^ (prefixWord ++ tailWord_4389710).sum := by decide
  have hdescent : baseEnd_4389710 < baseStart_4389710 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389767 : List Nat := [1, 1, 4, 2, 3, 1, 1, 1, 4, 2, 3]
def baseStart_4389767 : Nat := 118140960795 + 4389767 * 2 ^ 59
def prefixEnd_4389767 : Nat := 4983230072969 + 3 ^ 40 * 4389767 * 2
def baseEnd_4389767 : Nat := 2254060432245431750124335

theorem tailTrace_4389767 : CollatzResearch.WordTrace tailWord_4389767 prefixEnd_4389767 2254060432245431750124335 := by
  unfold tailWord_4389767
  simp only [CollatzResearch.WordTrace]
  refine ⟨160107955887631346361047555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106738637258420897574031703 160107955887631346361047555)
  ·
    refine ⟨240161933831447019541571333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160107955887631346361047555 240161933831447019541571333)
    ·
      refine ⟨45030362593396316164044625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 240161933831447019541571333 45030362593396316164044625)
      ·
        refine ⟨33772771945047237123033469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45030362593396316164044625 33772771945047237123033469)
        ·
          refine ⟨12664789479392713921137551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33772771945047237123033469 12664789479392713921137551)
          ·
            refine ⟨18997184219089070881706327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12664789479392713921137551 18997184219089070881706327)
            ·
              refine ⟨28495776328633606322559491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18997184219089070881706327 28495776328633606322559491)
              ·
                refine ⟨42743664492950409483839237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28495776328633606322559491 42743664492950409483839237)
                ·
                  refine ⟨8014437092428201778219857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42743664492950409483839237 8014437092428201778219857)
                  ·
                    refine ⟨6010827819321151333664893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8014437092428201778219857 6010827819321151333664893)
                    ·
                      refine ⟨2254060432245431750124335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6010827819321151333664893 2254060432245431750124335)
                      ·
                        rfl

theorem cell23_4389767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_4389767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389767 prefixEnd_4389767 := by exact prefixLift 4389767
  have htrace : WordTrace (prefixWord ++ tailWord_4389767) baseStart_4389767 baseEnd_4389767 := by
    simpa [prefixWord, tailWord_4389767, baseEnd_4389767] using wordTrace_append hprefix tailTrace_4389767
  have hstable : (prefixWord ++ tailWord_4389767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389767).length < 2 ^ (prefixWord ++ tailWord_4389767).sum := by decide
  have hdescent : baseEnd_4389767 < baseStart_4389767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389824 : List Nat := [2, 1, 1, 2, 3, 3, 2, 2, 2, 3, 2]
def baseStart_4389824 : Nat := 118140960795 + 4389824 * 2 ^ 59
def prefixEnd_4389824 : Nat := 4983230072969 + 3 ^ 40 * 4389824 * 2
def baseEnd_4389824 : Nat := 2254089700642738027111573

theorem tailTrace_4389824 : CollatzResearch.WordTrace tailWord_4389824 prefixEnd_4389824 2254089700642738027111573 := by
  unfold tailWord_4389824
  simp only [CollatzResearch.WordTrace]
  refine ⟨80055017424212422547936263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106740023232283230063915017 80055017424212422547936263)
  ·
    refine ⟨120082526136318633821904395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80055017424212422547936263 120082526136318633821904395)
    ·
      refine ⟨180123789204477950732856593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120082526136318633821904395 180123789204477950732856593)
      ·
        refine ⟨135092841903358463049642445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180123789204477950732856593 135092841903358463049642445)
        ·
          refine ⟨50659815713759423643615917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135092841903358463049642445 50659815713759423643615917)
          ·
            refine ⟨18997430892659783866355969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50659815713759423643615917 18997430892659783866355969)
            ·
              refine ⟨14248073169494837899766977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18997430892659783866355969 14248073169494837899766977)
              ·
                refine ⟨10686054877121128424825233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14248073169494837899766977 10686054877121128424825233)
                ·
                  refine ⟨8014541157840846318618925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10686054877121128424825233 8014541157840846318618925)
                  ·
                    refine ⟨3005452934190317369482097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8014541157840846318618925 3005452934190317369482097)
                    ·
                      refine ⟨2254089700642738027111573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3005452934190317369482097 2254089700642738027111573)
                      ·
                        rfl

theorem cell23_4389824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 2, 3, 2].length) (baseStart_4389824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389824 prefixEnd_4389824 := by exact prefixLift 4389824
  have htrace : WordTrace (prefixWord ++ tailWord_4389824) baseStart_4389824 baseEnd_4389824 := by
    simpa [prefixWord, tailWord_4389824, baseEnd_4389824] using wordTrace_append hprefix tailTrace_4389824
  have hstable : (prefixWord ++ tailWord_4389824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389824).length < 2 ^ (prefixWord ++ tailWord_4389824).sum := by decide
  have hdescent : baseEnd_4389824 < baseStart_4389824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389840 : List Nat := [2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 5]
def baseStart_4389840 : Nat := 118140960795 + 4389840 * 2 ^ 59
def prefixEnd_4389840 : Nat := 4983230072969 + 3 ^ 40 * 4389840 * 2
def baseEnd_4389840 : Nat := 2254097916333209964511499

theorem tailTrace_4389840 : CollatzResearch.WordTrace tailWord_4389840 prefixEnd_4389840 2254097916333209964511499 := by
  unfold tailWord_4389840
  simp only [CollatzResearch.WordTrace]
  refine ⟨80055309208183439914227487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106740412277577919885636649 80055309208183439914227487)
  ·
    refine ⟨120082963812275159871341231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80055309208183439914227487 120082963812275159871341231)
    ·
      refine ⟨180124445718412739807011847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120082963812275159871341231 180124445718412739807011847)
      ·
        refine ⟨270186668577619109710517771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180124445718412739807011847 270186668577619109710517771)
        ·
          refine ⟨405280002866428664565776657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270186668577619109710517771 405280002866428664565776657)
          ·
            refine ⟨303960002149821498424332493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 405280002866428664565776657 303960002149821498424332493)
            ·
              refine ⟨113985000806183061909124685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 303960002149821498424332493 113985000806183061909124685)
              ·
                refine ⟨42744375302318648215921757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113985000806183061909124685 42744375302318648215921757)
                ·
                  refine ⟨16029140738369493080970659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42744375302318648215921757 16029140738369493080970659)
                  ·
                    refine ⟨24043711107554239621455989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16029140738369493080970659 24043711107554239621455989)
                    ·
                      refine ⟨2254097916333209964511499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24043711107554239621455989 2254097916333209964511499)
                      ·
                        rfl

theorem cell23_4389840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 5].length) (baseStart_4389840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389840 prefixEnd_4389840 := by exact prefixLift 4389840
  have htrace : WordTrace (prefixWord ++ tailWord_4389840) baseStart_4389840 baseEnd_4389840 := by
    simpa [prefixWord, tailWord_4389840, baseEnd_4389840] using wordTrace_append hprefix tailTrace_4389840
  have hstable : (prefixWord ++ tailWord_4389840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389840).length < 2 ^ (prefixWord ++ tailWord_4389840).sum := by decide
  have hdescent : baseEnd_4389840 < baseStart_4389840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389858 : List Nat := [3, 3, 3, 1, 1, 1, 3, 1, 2, 3, 2]
def baseStart_4389858 : Nat := 118140960795 + 4389858 * 2 ^ 59
def prefixEnd_4389858 : Nat := 4983230072969 + 3 ^ 40 * 4389858 * 2
def baseEnd_4389858 : Nat := 2254107158984990894086417

theorem tailTrace_4389858 : CollatzResearch.WordTrace tailWord_4389858 prefixEnd_4389858 2254107158984990894086417 := by
  unfold tailWord_4389858
  simp only [CollatzResearch.WordTrace]
  refine ⟨40027818732575417225652557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106740849953534445935073485 40027818732575417225652557)
  ·
    refine ⟨15010432024715781459619709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40027818732575417225652557 15010432024715781459619709)
    ·
      refine ⟨5628912009268418047357391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15010432024715781459619709 5628912009268418047357391)
      ·
        refine ⟨8443368013902627071036087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5628912009268418047357391 8443368013902627071036087)
        ·
          refine ⟨12665052020853940606554131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8443368013902627071036087 12665052020853940606554131)
          ·
            refine ⟨18997578031280910909831197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12665052020853940606554131 18997578031280910909831197)
            ·
              refine ⟨7124091761730341591186699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18997578031280910909831197 7124091761730341591186699)
              ·
                refine ⟨10686137642595512386780049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7124091761730341591186699 10686137642595512386780049)
                ·
                  refine ⟨8014603231946634290085037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10686137642595512386780049 8014603231946634290085037)
                  ·
                    refine ⟨3005476211979987858781889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8014603231946634290085037 3005476211979987858781889)
                    ·
                      refine ⟨2254107158984990894086417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3005476211979987858781889 2254107158984990894086417)
                      ·
                        rfl

theorem cell23_4389858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_4389858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389858 prefixEnd_4389858 := by exact prefixLift 4389858
  have htrace : WordTrace (prefixWord ++ tailWord_4389858) baseStart_4389858 baseEnd_4389858 := by
    simpa [prefixWord, tailWord_4389858, baseEnd_4389858] using wordTrace_append hprefix tailTrace_4389858
  have hstable : (prefixWord ++ tailWord_4389858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389858).length < 2 ^ (prefixWord ++ tailWord_4389858).sum := by decide
  have hdescent : baseEnd_4389858 < baseStart_4389858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389871 : List Nat := [1, 1, 2, 1, 4, 5, 2, 1, 1, 1, 4]
def baseStart_4389871 : Nat := 118140960795 + 4389871 * 2 ^ 59
def prefixEnd_4389871 : Nat := 4983230072969 + 3 ^ 40 * 4389871 * 2
def baseEnd_4389871 : Nat := 2254113834233499343223857

theorem tailTrace_4389871 : CollatzResearch.WordTrace tailWord_4389871 prefixEnd_4389871 2254113834233499343223857 := by
  unfold tailWord_4389871
  simp only [CollatzResearch.WordTrace]
  refine ⟨160111749079254572122833467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106741166052836381415222311 160111749079254572122833467)
  ·
    refine ⟨240167623618881858184250201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160111749079254572122833467 240167623618881858184250201)
    ·
      refine ⟨180125717714161393638187651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240167623618881858184250201 180125717714161393638187651)
      ·
        refine ⟨270188576571242090457281477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180125717714161393638187651 270188576571242090457281477)
        ·
          refine ⟨50660358107107891960740277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 270188576571242090457281477 50660358107107891960740277)
          ·
            refine ⟨4749408572541364871319401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50660358107107891960740277 4749408572541364871319401)
            ·
              refine ⟨3562056429406023653489551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4749408572541364871319401 3562056429406023653489551)
              ·
                refine ⟨5343084644109035480234327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3562056429406023653489551 5343084644109035480234327)
                ·
                  refine ⟨8014626966163553220351491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5343084644109035480234327 8014626966163553220351491)
                  ·
                    refine ⟨12021940449245329830527237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8014626966163553220351491 12021940449245329830527237)
                    ·
                      refine ⟨2254113834233499343223857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12021940449245329830527237 2254113834233499343223857)
                      ·
                        rfl

theorem cell23_4389871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 1, 1, 1, 4].length) (baseStart_4389871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389871 prefixEnd_4389871 := by exact prefixLift 4389871
  have htrace : WordTrace (prefixWord ++ tailWord_4389871) baseStart_4389871 baseEnd_4389871 := by
    simpa [prefixWord, tailWord_4389871, baseEnd_4389871] using wordTrace_append hprefix tailTrace_4389871
  have hstable : (prefixWord ++ tailWord_4389871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389871).length < 2 ^ (prefixWord ++ tailWord_4389871).sum := by decide
  have hdescent : baseEnd_4389871 < baseStart_4389871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389880 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 2, 2, 6]
def baseStart_4389880 : Nat := 118140960795 + 4389880 * 2 ^ 59
def prefixEnd_4389880 : Nat := 4983230072969 + 3 ^ 40 * 4389880 * 2
def baseEnd_4389880 : Nat := 2254118455559389808011315

theorem tailTrace_4389880 : CollatzResearch.WordTrace tailWord_4389880 prefixEnd_4389880 2254118455559389808011315 := by
  unfold tailWord_4389880
  simp only [CollatzResearch.WordTrace]
  refine ⟨80056038668110983329955547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106741384890814644439940729 80056038668110983329955547)
  ·
    refine ⟨120084058002166474994933321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80056038668110983329955547 120084058002166474994933321)
    ·
      refine ⟨90063043501624856246199991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120084058002166474994933321 90063043501624856246199991)
      ·
        refine ⟨135094565252437284369299987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90063043501624856246199991 135094565252437284369299987)
        ·
          refine ⟨202641847878655926553949981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135094565252437284369299987 202641847878655926553949981)
          ·
            refine ⟨75990692954495972457731243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 202641847878655926553949981 75990692954495972457731243)
            ·
              refine ⟨113986039431743958686596865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75990692954495972457731243 113986039431743958686596865)
              ·
                refine ⟨85489529573807969014947649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113986039431743958686596865 85489529573807969014947649)
                ·
                  refine ⟨64117147180355976761210737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85489529573807969014947649 64117147180355976761210737)
                  ·
                    refine ⟨48087860385266982570908053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64117147180355976761210737 48087860385266982570908053)
                    ·
                      refine ⟨2254118455559389808011315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48087860385266982570908053 2254118455559389808011315)
                      ·
                        rfl

theorem cell23_4389880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 2, 2, 6].length) (baseStart_4389880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389880 prefixEnd_4389880 := by exact prefixLift 4389880
  have htrace : WordTrace (prefixWord ++ tailWord_4389880) baseStart_4389880 baseEnd_4389880 := by
    simpa [prefixWord, tailWord_4389880, baseEnd_4389880] using wordTrace_append hprefix tailTrace_4389880
  have hstable : (prefixWord ++ tailWord_4389880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389880).length < 2 ^ (prefixWord ++ tailWord_4389880).sum := by decide
  have hdescent : baseEnd_4389880 < baseStart_4389880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389957 : List Nat := [1, 3, 1, 1, 1, 3, 2, 3, 2, 2, 4]
def baseStart_4389957 : Nat := 118140960795 + 4389957 * 2 ^ 59
def prefixEnd_4389957 : Nat := 4983230072969 + 3 ^ 40 * 4389957 * 2
def baseEnd_4389957 : Nat := 2254157993569786006748461

theorem tailTrace_4389957 : CollatzResearch.WordTrace tailWord_4389957 prefixEnd_4389957 2254157993569786006748461 := by
  unfold tailWord_4389957
  simp only [CollatzResearch.WordTrace]
  refine ⟨160114885756943008810464125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106743257171295339206976083 160114885756943008810464125)
  ·
    refine ⟨60043082158853628303924047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160114885756943008810464125 60043082158853628303924047)
    ·
      refine ⟨90064623238280442455886071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60043082158853628303924047 90064623238280442455886071)
      ·
        refine ⟨135096934857420663683829107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90064623238280442455886071 135096934857420663683829107)
        ·
          refine ⟨202645402286130995525743661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135096934857420663683829107 202645402286130995525743661)
          ·
            refine ⟨75992025857299123322153873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 202645402286130995525743661 75992025857299123322153873)
            ·
              refine ⟨56994019392974342491615405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75992025857299123322153873 56994019392974342491615405)
              ·
                refine ⟨21372757272365378434355777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56994019392974342491615405 21372757272365378434355777)
                ·
                  refine ⟨16029567954274033825766833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21372757272365378434355777 16029567954274033825766833)
                  ·
                    refine ⟨12022175965705525369325125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16029567954274033825766833 12022175965705525369325125)
                    ·
                      refine ⟨2254157993569786006748461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12022175965705525369325125 2254157993569786006748461)
                      ·
                        rfl

theorem cell23_4389957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 2, 4].length) (baseStart_4389957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389957 prefixEnd_4389957 := by exact prefixLift 4389957
  have htrace : WordTrace (prefixWord ++ tailWord_4389957) baseStart_4389957 baseEnd_4389957 := by
    simpa [prefixWord, tailWord_4389957, baseEnd_4389957] using wordTrace_append hprefix tailTrace_4389957
  have hstable : (prefixWord ++ tailWord_4389957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389957).length < 2 ^ (prefixWord ++ tailWord_4389957).sum := by decide
  have hdescent : baseEnd_4389957 < baseStart_4389957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389965 : List Nat := [1, 6, 1, 1, 1, 4, 1, 2, 1, 3, 2]
def baseStart_4389965 : Nat := 118140960795 + 4389965 * 2 ^ 59
def prefixEnd_4389965 : Nat := 4983230072969 + 3 ^ 40 * 4389965 * 2
def baseEnd_4389965 : Nat := 2254162101415021975448425

theorem tailTrace_4389965 : CollatzResearch.WordTrace tailWord_4389965 prefixEnd_4389965 2254162101415021975448425 := by
  unfold tailWord_4389965
  simp only [CollatzResearch.WordTrace]
  refine ⟨160115177540914026176755349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106743451693942684117836899 160115177540914026176755349)
  ·
    refine ⟨7505398947230344977035407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 160115177540914026176755349 7505398947230344977035407)
    ·
      refine ⟨11258098420845517465553111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7505398947230344977035407 11258098420845517465553111)
      ·
        refine ⟨16887147631268276198329667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11258098420845517465553111 16887147631268276198329667)
        ·
          refine ⟨25330721446902414297494501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16887147631268276198329667 25330721446902414297494501)
          ·
            refine ⟨4749510271294202680780219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25330721446902414297494501 4749510271294202680780219)
            ·
              refine ⟨7124265406941304021170329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4749510271294202680780219 7124265406941304021170329)
              ·
                refine ⟨5343199055205978015877747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7124265406941304021170329 5343199055205978015877747)
                ·
                  refine ⟨8014798582808967023816621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5343199055205978015877747 8014798582808967023816621)
                  ·
                    refine ⟨3005549468553362633931233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8014798582808967023816621 3005549468553362633931233)
                    ·
                      refine ⟨2254162101415021975448425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3005549468553362633931233 2254162101415021975448425)
                      ·
                        rfl

theorem cell23_4389965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_4389965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389965 prefixEnd_4389965 := by exact prefixLift 4389965
  have htrace : WordTrace (prefixWord ++ tailWord_4389965) baseStart_4389965 baseEnd_4389965 := by
    simpa [prefixWord, tailWord_4389965, baseEnd_4389965] using wordTrace_append hprefix tailTrace_4389965
  have hstable : (prefixWord ++ tailWord_4389965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389965).length < 2 ^ (prefixWord ++ tailWord_4389965).sum := by decide
  have hdescent : baseEnd_4389965 < baseStart_4389965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389977 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 3, 5, 3]
def baseStart_4389977 : Nat := 118140960795 + 4389977 * 2 ^ 59
def prefixEnd_4389977 : Nat := 4983230072969 + 3 ^ 40 * 4389977 * 2
def baseEnd_4389977 : Nat := 2254168263182875928498369

theorem tailTrace_4389977 : CollatzResearch.WordTrace tailWord_4389977 prefixEnd_4389977 2254168263182875928498369 := by
  unfold tailWord_4389977
  simp only [CollatzResearch.WordTrace]
  refine ⟨160115615216870552226192185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106743743477913701484128123 160115615216870552226192185)
  ·
    refine ⟨120086711412652914169644139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160115615216870552226192185 120086711412652914169644139)
    ·
      refine ⟨180130067118979371254466209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120086711412652914169644139 180130067118979371254466209)
      ·
        refine ⟨135097550339234528440849657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180130067118979371254466209 135097550339234528440849657)
        ·
          refine ⟨101323162754425896330637243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135097550339234528440849657 101323162754425896330637243)
          ·
            refine ⟨151984744131638844495955865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101323162754425896330637243 151984744131638844495955865)
            ·
              refine ⟨113988558098729133371966899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151984744131638844495955865 113988558098729133371966899)
              ·
                refine ⟨170982837148093700057950349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113988558098729133371966899 170982837148093700057950349)
                ·
                  refine ⟨64118563930535137521731381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 170982837148093700057950349 64118563930535137521731381)
                  ·
                    refine ⟨6011115368487669142662317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 64118563930535137521731381 6011115368487669142662317)
                    ·
                      refine ⟨2254168263182875928498369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6011115368487669142662317 2254168263182875928498369)
                      ·
                        rfl

theorem cell23_4389977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 5, 3].length) (baseStart_4389977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389977 prefixEnd_4389977 := by exact prefixLift 4389977
  have htrace : WordTrace (prefixWord ++ tailWord_4389977) baseStart_4389977 baseEnd_4389977 := by
    simpa [prefixWord, tailWord_4389977, baseEnd_4389977] using wordTrace_append hprefix tailTrace_4389977
  have hstable : (prefixWord ++ tailWord_4389977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389977).length < 2 ^ (prefixWord ++ tailWord_4389977).sum := by decide
  have hdescent : baseEnd_4389977 < baseStart_4389977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4389984 : List Nat := [2, 1, 1, 3, 2, 2, 2, 5, 5]
def baseStart_4389984 : Nat := 118140960795 + 4389984 * 2 ^ 59
def prefixEnd_4389984 : Nat := 4983230072969 + 3 ^ 40 * 4389984 * 2
def baseEnd_4389984 : Nat := 250463539727495266790093

theorem tailTrace_4389984 : CollatzResearch.WordTrace tailWord_4389984 prefixEnd_4389984 250463539727495266790093 := by
  unfold tailWord_4389984
  simp only [CollatzResearch.WordTrace]
  refine ⟨80057935263922596210848503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106743913685230128281131337 80057935263922596210848503)
  ·
    refine ⟨120086902895883894316272755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80057935263922596210848503 120086902895883894316272755)
    ·
      refine ⟨180130354343825841474409133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120086902895883894316272755 180130354343825841474409133)
      ·
        refine ⟨67548882878934690552903425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 180130354343825841474409133 67548882878934690552903425)
        ·
          refine ⟨50661662159201017914677569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67548882878934690552903425 50661662159201017914677569)
          ·
            refine ⟨37996246619400763436008177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50661662159201017914677569 37996246619400763436008177)
            ·
              refine ⟨28497184964550572577006133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37996246619400763436008177 28497184964550572577006133)
              ·
                refine ⟨2671611090426616179094325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28497184964550572577006133 2671611090426616179094325)
                ·
                  refine ⟨250463539727495266790093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2671611090426616179094325 250463539727495266790093)
                  ·
                    rfl

theorem cell23_4389984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 5, 5].length) (baseStart_4389984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4389984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4389984 prefixEnd_4389984 := by exact prefixLift 4389984
  have htrace : WordTrace (prefixWord ++ tailWord_4389984) baseStart_4389984 baseEnd_4389984 := by
    simpa [prefixWord, tailWord_4389984, baseEnd_4389984] using wordTrace_append hprefix tailTrace_4389984
  have hstable : (prefixWord ++ tailWord_4389984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4389984).length < 2 ^ (prefixWord ++ tailWord_4389984).sum := by decide
  have hdescent : baseEnd_4389984 < baseStart_4389984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4389984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390007 : List Nat := [1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 5]
def baseStart_4390007 : Nat := 118140960795 + 4390007 * 2 ^ 59
def prefixEnd_4390007 : Nat := 4983230072969 + 3 ^ 40 * 4390007 * 2
def baseEnd_4390007 : Nat := 2254183667602510811123231

theorem tailTrace_4390007 : CollatzResearch.WordTrace tailWord_4390007 prefixEnd_4390007 2254183667602510811123231 := by
  unfold tailWord_4390007
  simp only [CollatzResearch.WordTrace]
  refine ⟨160116709406761867349784275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106744472937841244899856183 160116709406761867349784275)
  ·
    refine ⟨240175064110142801024676413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160116709406761867349784275 240175064110142801024676413)
    ·
      refine ⟨90065649041303550384253655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 240175064110142801024676413 90065649041303550384253655)
      ·
        refine ⟨135098473561955325576380483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90065649041303550384253655 135098473561955325576380483)
        ·
          refine ⟨202647710342932988364570725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135098473561955325576380483 202647710342932988364570725)
          ·
            refine ⟨37996445689299935318357011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 202647710342932988364570725 37996445689299935318357011)
            ·
              refine ⟨56994668533949902977535517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37996445689299935318357011 56994668533949902977535517)
              ·
                refine ⟨21373000700231213616575819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56994668533949902977535517 21373000700231213616575819)
                ·
                  refine ⟨32059501050346820424863729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21373000700231213616575819 32059501050346820424863729)
                  ·
                    refine ⟨24044625787760115318647797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32059501050346820424863729 24044625787760115318647797)
                    ·
                      refine ⟨2254183667602510811123231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24044625787760115318647797 2254183667602510811123231)
                      ·
                        rfl

theorem cell23_4390007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 5].length) (baseStart_4390007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390007 prefixEnd_4390007 := by exact prefixLift 4390007
  have htrace : WordTrace (prefixWord ++ tailWord_4390007) baseStart_4390007 baseEnd_4390007 := by
    simpa [prefixWord, tailWord_4390007, baseEnd_4390007] using wordTrace_append hprefix tailTrace_4390007
  have hstable : (prefixWord ++ tailWord_4390007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390007).length < 2 ^ (prefixWord ++ tailWord_4390007).sum := by decide
  have hdescent : baseEnd_4390007 < baseStart_4390007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390037 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 2, 3, 5]
def baseStart_4390037 : Nat := 118140960795 + 4390037 * 2 ^ 59
def prefixEnd_4390037 : Nat := 4983230072969 + 3 ^ 40 * 4390037 * 2
def baseEnd_4390037 : Nat := 2254199072022145693748093

theorem tailTrace_4390037 : CollatzResearch.WordTrace tailWord_4390037 prefixEnd_4390037 2254199072022145693748093 := by
  unfold tailWord_4390037
  simp only [CollatzResearch.WordTrace]
  refine ⟨160117803596653182473376365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106745202397768788315584243 160117803596653182473376365)
  ·
    refine ⟨60044176348744943427516137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160117803596653182473376365 60044176348744943427516137)
    ·
      refine ⟨45033132261558707570637103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60044176348744943427516137 45033132261558707570637103)
      ·
        refine ⟨67549698392338061355955655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45033132261558707570637103 67549698392338061355955655)
        ·
          refine ⟨101324547588507092033933483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67549698392338061355955655 101324547588507092033933483)
          ·
            refine ⟨151986821382760638050900225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101324547588507092033933483 151986821382760638050900225)
            ·
              refine ⟨113990116037070478538175169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151986821382760638050900225 113990116037070478538175169)
              ·
                refine ⟨85492587027802858903631377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113990116037070478538175169 85492587027802858903631377)
                ·
                  refine ⟨64119440270852144177723533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85492587027802858903631377 64119440270852144177723533)
                  ·
                    refine ⟨24044790101569554066646325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64119440270852144177723533 24044790101569554066646325)
                    ·
                      refine ⟨2254199072022145693748093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24044790101569554066646325 2254199072022145693748093)
                      ·
                        rfl

theorem cell23_4390037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_4390037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390037 prefixEnd_4390037 := by exact prefixLift 4390037
  have htrace : WordTrace (prefixWord ++ tailWord_4390037) baseStart_4390037 baseEnd_4390037 := by
    simpa [prefixWord, tailWord_4390037, baseEnd_4390037] using wordTrace_append hprefix tailTrace_4390037
  have hstable : (prefixWord ++ tailWord_4390037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390037).length < 2 ^ (prefixWord ++ tailWord_4390037).sum := by decide
  have hdescent : baseEnd_4390037 < baseStart_4390037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390087 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 2, 9]
def baseStart_4390087 : Nat := 118140960795 + 4390087 * 2 ^ 59
def prefixEnd_4390087 : Nat := 4983230072969 + 3 ^ 40 * 4390087 * 2
def baseEnd_4390087 : Nat := 751408248684956832707621

theorem tailTrace_4390087 : CollatzResearch.WordTrace tailWord_4390087 prefixEnd_4390087 751408248684956832707621 := by
  unfold tailWord_4390087
  simp only [CollatzResearch.WordTrace]
  refine ⟨160119627246472041012696515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106746418164314694008464343 160119627246472041012696515)
  ·
    refine ⟨240179440869708061519044773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160119627246472041012696515 240179440869708061519044773)
    ·
      refine ⟨45033645163070261534820895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 240179440869708061519044773 45033645163070261534820895)
      ·
        refine ⟨67550467744605392302231343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45033645163070261534820895 67550467744605392302231343)
        ·
          refine ⟨101325701616908088453347015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67550467744605392302231343 101325701616908088453347015)
          ·
            refine ⟨151988552425362132680020523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101325701616908088453347015 151988552425362132680020523)
            ·
              refine ⟨227982828638043199020030785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151988552425362132680020523 227982828638043199020030785)
              ·
                refine ⟨170987121478532399265023089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 227982828638043199020030785 170987121478532399265023089)
                ·
                  refine ⟨128240341108899299448767317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 170987121478532399265023089 128240341108899299448767317)
                  ·
                    refine ⟨751408248684956832707621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 128240341108899299448767317 751408248684956832707621)
                    ·
                      rfl

theorem cell23_4390087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_4390087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390087 prefixEnd_4390087 := by exact prefixLift 4390087
  have htrace : WordTrace (prefixWord ++ tailWord_4390087) baseStart_4390087 baseEnd_4390087 := by
    simpa [prefixWord, tailWord_4390087, baseEnd_4390087] using wordTrace_append hprefix tailTrace_4390087
  have hstable : (prefixWord ++ tailWord_4390087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390087).length < 2 ^ (prefixWord ++ tailWord_4390087).sum := by decide
  have hdescent : baseEnd_4390087 < baseStart_4390087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390111 : List Nat := [1, 1, 2, 3, 2, 1, 3, 1, 4, 3, 2]
def baseStart_4390111 : Nat := 118140960795 + 4390111 * 2 ^ 59
def prefixEnd_4390111 : Nat := 4983230072969 + 3 ^ 40 * 4390111 * 2
def baseEnd_4390111 : Nat := 2254237069590578404222753

theorem tailTrace_4390111 : CollatzResearch.WordTrace tailWord_4390111 prefixEnd_4390111 2254237069590578404222753 := by
  unfold tailWord_4390111
  simp only [CollatzResearch.WordTrace]
  refine ⟨160120502598385093111570187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106747001732256728741046791 160120502598385093111570187)
  ·
    refine ⟨240180753897577639667355281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160120502598385093111570187 240180753897577639667355281)
    ·
      refine ⟨180135565423183229750516461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240180753897577639667355281 180135565423183229750516461)
      ·
        refine ⟨67550837033693711156443673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 180135565423183229750516461 67550837033693711156443673)
        ·
          refine ⟨50663127775270283367332755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67550837033693711156443673 50663127775270283367332755)
          ·
            refine ⟨75994691662905425050999133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50663127775270283367332755 75994691662905425050999133)
            ·
              refine ⟨28498009373589534394124675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75994691662905425050999133 28498009373589534394124675)
              ·
                refine ⟨42747014060384301591187013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28498009373589534394124675 42747014060384301591187013)
                ·
                  refine ⟨8015065136322056548347565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42747014060384301591187013 8015065136322056548347565)
                  ·
                    refine ⟨3005649426120771205630337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8015065136322056548347565 3005649426120771205630337)
                    ·
                      refine ⟨2254237069590578404222753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3005649426120771205630337 2254237069590578404222753)
                      ·
                        rfl

theorem cell23_4390111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 3, 2].length) (baseStart_4390111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390111 prefixEnd_4390111 := by exact prefixLift 4390111
  have htrace : WordTrace (prefixWord ++ tailWord_4390111) baseStart_4390111 baseEnd_4390111 := by
    simpa [prefixWord, tailWord_4390111, baseEnd_4390111] using wordTrace_append hprefix tailTrace_4390111
  have hstable : (prefixWord ++ tailWord_4390111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390111).length < 2 ^ (prefixWord ++ tailWord_4390111).sum := by decide
  have hdescent : baseEnd_4390111 < baseStart_4390111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390168 : List Nat := [2, 1, 2, 3, 1, 4, 2, 2, 2, 4]
def baseStart_4390168 : Nat := 118140960795 + 4390168 * 2 ^ 59
def prefixEnd_4390168 : Nat := 4983230072969 + 3 ^ 40 * 4390168 * 2
def baseEnd_4390168 : Nat := 751422112662628227069997

theorem tailTrace_4390168 : CollatzResearch.WordTrace tailWord_4390168 prefixEnd_4390168 751422112662628227069997 := by
  unfold tailWord_4390168
  simp only [CollatzResearch.WordTrace]
  refine ⟨80061290779589295923197579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106748387706119061230930105 80061290779589295923197579)
  ·
    refine ⟨120091936169383943884796369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80061290779589295923197579 120091936169383943884796369)
    ·
      refine ⟨90068952127037957913597277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120091936169383943884796369 90068952127037957913597277)
      ·
        refine ⟨33775857047639234217598979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90068952127037957913597277 33775857047639234217598979)
        ·
          refine ⟨50663785571458851326398469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33775857047639234217598979 50663785571458851326398469)
          ·
            refine ⟨9499459794648534623699713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50663785571458851326398469 9499459794648534623699713)
            ·
              refine ⟨7124594845986400967774785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9499459794648534623699713 7124594845986400967774785)
              ·
                refine ⟨5343446134489800725831089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7124594845986400967774785 5343446134489800725831089)
                ·
                  refine ⟨4007584600867350544373317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5343446134489800725831089 4007584600867350544373317)
                  ·
                    refine ⟨751422112662628227069997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4007584600867350544373317 751422112662628227069997)
                    ·
                      rfl

theorem cell23_4390168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 2, 4].length) (baseStart_4390168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390168 prefixEnd_4390168 := by exact prefixLift 4390168
  have htrace : WordTrace (prefixWord ++ tailWord_4390168) baseStart_4390168 baseEnd_4390168 := by
    simpa [prefixWord, tailWord_4390168, baseEnd_4390168] using wordTrace_append hprefix tailTrace_4390168
  have hstable : (prefixWord ++ tailWord_4390168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390168).length < 2 ^ (prefixWord ++ tailWord_4390168).sum := by decide
  have hdescent : baseEnd_4390168 < baseStart_4390168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390181 : List Nat := [1, 3, 1, 2, 4, 3, 1, 8]
def baseStart_4390181 : Nat := 118140960795 + 4390181 * 2 ^ 59
def prefixEnd_4390181 : Nat := 4983230072969 + 3 ^ 40 * 4390181 * 2
def baseEnd_4390181 : Nat := 83491593082829375198053

theorem tailTrace_4390181 : CollatzResearch.WordTrace tailWord_4390181 prefixEnd_4390181 83491593082829375198053 := by
  unfold tailWord_4390181
  simp only [CollatzResearch.WordTrace]
  refine ⟨160123055708131495066618397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106748703805420996711078931 160123055708131495066618397)
  ·
    refine ⟨60046145890549310649981899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160123055708131495066618397 60046145890549310649981899)
    ·
      refine ⟨90069218835823965974972849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60046145890549310649981899 90069218835823965974972849)
      ·
        refine ⟨67551914126867974481229637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90069218835823965974972849 67551914126867974481229637)
        ·
          refine ⟨12665983898787745215230557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67551914126867974481229637 12665983898787745215230557)
          ·
            refine ⟨4749743962045404455711459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12665983898787745215230557 4749743962045404455711459)
            ·
              refine ⟨7124615943068106683567189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4749743962045404455711459 7124615943068106683567189)
              ·
                refine ⟨83491593082829375198053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7124615943068106683567189 83491593082829375198053)
                ·
                  rfl

theorem cell23_4390181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 8].length) (baseStart_4390181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390181 prefixEnd_4390181 := by exact prefixLift 4390181
  have htrace : WordTrace (prefixWord ++ tailWord_4390181) baseStart_4390181 baseEnd_4390181 := by
    simpa [prefixWord, tailWord_4390181, baseEnd_4390181] using wordTrace_append hprefix tailTrace_4390181
  have hstable : (prefixWord ++ tailWord_4390181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390181).length < 2 ^ (prefixWord ++ tailWord_4390181).sum := by decide
  have hdescent : baseEnd_4390181 < baseStart_4390181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390191 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 6, 1, 3]
def baseStart_4390191 : Nat := 118140960795 + 4390191 * 2 ^ 59
def prefixEnd_4390191 : Nat := 4983230072969 + 3 ^ 40 * 4390191 * 2
def baseEnd_4390191 : Nat := 2254278148042938091222385

theorem tailTrace_4390191 : CollatzResearch.WordTrace tailWord_4390191 prefixEnd_4390191 2254278148042938091222385 := by
  unfold tailWord_4390191
  simp only [CollatzResearch.WordTrace]
  refine ⟨160123420438095266774482427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106748946958730177849654951 160123420438095266774482427)
  ·
    refine ⟨240185130657142900161723641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160123420438095266774482427 240185130657142900161723641)
    ·
      refine ⟨180138847992857175121292731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240185130657142900161723641 180138847992857175121292731)
      ·
        refine ⟨270208271989285762681939097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180138847992857175121292731 270208271989285762681939097)
        ·
          refine ⟨202656203991964322011454323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 270208271989285762681939097 202656203991964322011454323)
          ·
            refine ⟨303984305987946483017181485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202656203991964322011454323 303984305987946483017181485)
            ·
              refine ⟨113994114745479931131443057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 303984305987946483017181485 113994114745479931131443057)
              ·
                refine ⟨85495586059109948348582293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113994114745479931131443057 85495586059109948348582293)
                ·
                  refine ⟨4007605596520778828839795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 85495586059109948348582293 4007605596520778828839795)
                  ·
                    refine ⟨6011408394781168243259693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4007605596520778828839795 6011408394781168243259693)
                    ·
                      refine ⟨2254278148042938091222385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6011408394781168243259693 2254278148042938091222385)
                      ·
                        rfl

theorem cell23_4390191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 6, 1, 3].length) (baseStart_4390191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390191 prefixEnd_4390191 := by exact prefixLift 4390191
  have htrace : WordTrace (prefixWord ++ tailWord_4390191) baseStart_4390191 baseEnd_4390191 := by
    simpa [prefixWord, tailWord_4390191, baseEnd_4390191] using wordTrace_append hprefix tailTrace_4390191
  have hstable : (prefixWord ++ tailWord_4390191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390191).length < 2 ^ (prefixWord ++ tailWord_4390191).sum := by decide
  have hdescent : baseEnd_4390191 < baseStart_4390191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390209 : List Nat := [1, 2, 5, 2, 1, 2, 2, 3, 1, 2, 2]
def baseStart_4390209 : Nat := 118140960795 + 4390209 * 2 ^ 59
def prefixEnd_4390209 : Nat := 4983230072969 + 3 ^ 40 * 4390209 * 2
def baseEnd_4390209 : Nat := 2254287390694719020797303

theorem tailTrace_4390209 : CollatzResearch.WordTrace tailWord_4390209 prefixEnd_4390209 2254287390694719020797303 := by
  unfold tailWord_4390209
  simp only [CollatzResearch.WordTrace]
  refine ⟨160124076952030055848637681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106749384634686703899091787 160124076952030055848637681)
  ·
    refine ⟨120093057714022541886478261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160124076952030055848637681 120093057714022541886478261)
    ·
      refine ⟨11258724160689613301857337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 120093057714022541886478261 11258724160689613301857337)
      ·
        refine ⟨8444043120517209976393003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11258724160689613301857337 8444043120517209976393003)
        ·
          refine ⟨12666064680775814964589505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8444043120517209976393003 12666064680775814964589505)
          ·
            refine ⟨9499548510581861223442129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12666064680775814964589505 9499548510581861223442129)
            ·
              refine ⟨7124661382936395917581597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9499548510581861223442129 7124661382936395917581597)
              ·
                refine ⟨2671748018601148469093099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7124661382936395917581597 2671748018601148469093099)
                ·
                  refine ⟨4007622027901722703639649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2671748018601148469093099 4007622027901722703639649)
                  ·
                    refine ⟨3005716520926292027729737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4007622027901722703639649 3005716520926292027729737)
                    ·
                      refine ⟨2254287390694719020797303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3005716520926292027729737 2254287390694719020797303)
                      ·
                        rfl

theorem cell23_4390209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_4390209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390209 prefixEnd_4390209 := by exact prefixLift 4390209
  have htrace : WordTrace (prefixWord ++ tailWord_4390209) baseStart_4390209 baseEnd_4390209 := by
    simpa [prefixWord, tailWord_4390209, baseEnd_4390209] using wordTrace_append hprefix tailTrace_4390209
  have hstable : (prefixWord ++ tailWord_4390209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390209).length < 2 ^ (prefixWord ++ tailWord_4390209).sum := by decide
  have hdescent : baseEnd_4390209 < baseStart_4390209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390212 : List Nat := [2, 3, 4, 1, 1, 1, 4, 1, 1, 2, 3]
def baseStart_4390212 : Nat := 118140960795 + 4390212 * 2 ^ 59
def prefixEnd_4390212 : Nat := 4983230072969 + 3 ^ 40 * 4390212 * 2
def baseEnd_4390212 : Nat := 2254288931136682509059789

theorem tailTrace_4390212 : CollatzResearch.WordTrace tailWord_4390212 prefixEnd_4390212 2254288931136682509059789 := by
  unfold tailWord_4390212
  simp only [CollatzResearch.WordTrace]
  refine ⟨80062093185509593680498445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106749457580679458240664593 80062093185509593680498445)
  ·
    refine ⟨30023284944566097630186917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80062093185509593680498445 30023284944566097630186917)
    ·
      refine ⟨5629365927106143305660047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30023284944566097630186917 5629365927106143305660047)
      ·
        refine ⟨8444048890659214958490071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5629365927106143305660047 8444048890659214958490071)
        ·
          refine ⟨12666073335988822437735107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8444048890659214958490071 12666073335988822437735107)
          ·
            refine ⟨18999110003983233656602661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12666073335988822437735107 18999110003983233656602661)
            ·
              refine ⟨3562333125746856310612999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18999110003983233656602661 3562333125746856310612999)
              ·
                refine ⟨5343499688620284465919499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3562333125746856310612999 5343499688620284465919499)
                ·
                  refine ⟨8015249532930426698879249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5343499688620284465919499 8015249532930426698879249)
                  ·
                    refine ⟨6011437149697820024159437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8015249532930426698879249 6011437149697820024159437)
                    ·
                      refine ⟨2254288931136682509059789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6011437149697820024159437 2254288931136682509059789)
                      ·
                        rfl

theorem cell23_4390212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_4390212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390212 prefixEnd_4390212 := by exact prefixLift 4390212
  have htrace : WordTrace (prefixWord ++ tailWord_4390212) baseStart_4390212 baseEnd_4390212 := by
    simpa [prefixWord, tailWord_4390212, baseEnd_4390212] using wordTrace_append hprefix tailTrace_4390212
  have hstable : (prefixWord ++ tailWord_4390212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390212).length < 2 ^ (prefixWord ++ tailWord_4390212).sum := by decide
  have hdescent : baseEnd_4390212 < baseStart_4390212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390224 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 4, 6]
def baseStart_4390224 : Nat := 118140960795 + 4390224 * 2 ^ 59
def prefixEnd_4390224 : Nat := 4983230072969 + 3 ^ 40 * 4390224 * 2
def baseEnd_4390224 : Nat := 751431697634845487369911

theorem tailTrace_4390224 : CollatzResearch.WordTrace tailWord_4390224 prefixEnd_4390224 751431697634845487369911 := by
  unfold tailWord_4390224
  simp only [CollatzResearch.WordTrace]
  refine ⟨80062312023487856705216863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106749749364650475606955817 80062312023487856705216863)
  ·
    refine ⟨120093468035231785057825295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80062312023487856705216863 120093468035231785057825295)
    ·
      refine ⟨180140202052847677586737943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120093468035231785057825295 180140202052847677586737943)
      ·
        refine ⟨270210303079271516380106915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180140202052847677586737943 270210303079271516380106915)
        ·
          refine ⟨405315454618907274570160373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270210303079271516380106915 405315454618907274570160373)
          ·
            refine ⟨37998323870522556990952535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 405315454618907274570160373 37998323870522556990952535)
            ·
              refine ⟨56997485805783835486428803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37998323870522556990952535 56997485805783835486428803)
              ·
                refine ⟨85496228708675753229643205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56997485805783835486428803 85496228708675753229643205)
                ·
                  refine ⟨16030542882876703730558101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85496228708675753229643205 16030542882876703730558101)
                  ·
                    refine ⟨751431697634845487369911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16030542882876703730558101 751431697634845487369911)
                    ·
                      rfl

theorem cell23_4390224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 4, 6].length) (baseStart_4390224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390224 prefixEnd_4390224 := by exact prefixLift 4390224
  have htrace : WordTrace (prefixWord ++ tailWord_4390224) baseStart_4390224 baseEnd_4390224 := by
    simpa [prefixWord, tailWord_4390224, baseEnd_4390224] using wordTrace_append hprefix tailTrace_4390224
  have hstable : (prefixWord ++ tailWord_4390224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390224).length < 2 ^ (prefixWord ++ tailWord_4390224).sum := by decide
  have hdescent : baseEnd_4390224 < baseStart_4390224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390242 : List Nat := [3, 3, 2, 1, 1, 1, 5, 1, 2, 1, 3]
def baseStart_4390242 : Nat := 118140960795 + 4390242 * 2 ^ 59
def prefixEnd_4390242 : Nat := 4983230072969 + 3 ^ 40 * 4390242 * 2
def baseEnd_4390242 : Nat := 2254304335556317391684651

theorem tailTrace_4390242 : CollatzResearch.WordTrace tailWord_4390242 prefixEnd_4390242 2254304335556317391684651 := by
  unfold tailWord_4390242
  simp only [CollatzResearch.WordTrace]
  refine ⟨40031320140227625621147245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106750187040607001656392653 40031320140227625621147245)
  ·
    refine ⟨15011745052585359607930217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40031320140227625621147245 15011745052585359607930217)
    ·
      refine ⟨11258808789439019705947663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15011745052585359607930217 11258808789439019705947663)
      ·
        refine ⟨16888213184158529558921495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11258808789439019705947663 16888213184158529558921495)
        ·
          refine ⟨25332319776237794338382243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16888213184158529558921495 25332319776237794338382243)
          ·
            refine ⟨37998479664356691507573365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25332319776237794338382243 37998479664356691507573365)
            ·
              refine ⟨3562357468533439828835003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37998479664356691507573365 3562357468533439828835003)
              ·
                refine ⟨5343536202800159743252505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3562357468533439828835003 5343536202800159743252505)
                ·
                  refine ⟨4007652152100119807439379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5343536202800159743252505 4007652152100119807439379)
                  ·
                    refine ⟨6011478228150179711159069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4007652152100119807439379 6011478228150179711159069)
                    ·
                      refine ⟨2254304335556317391684651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6011478228150179711159069 2254304335556317391684651)
                      ·
                        rfl

theorem cell23_4390242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_4390242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390242 prefixEnd_4390242 := by exact prefixLift 4390242
  have htrace : WordTrace (prefixWord ++ tailWord_4390242) baseStart_4390242 baseEnd_4390242 := by
    simpa [prefixWord, tailWord_4390242, baseEnd_4390242] using wordTrace_append hprefix tailTrace_4390242
  have hstable : (prefixWord ++ tailWord_4390242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390242).length < 2 ^ (prefixWord ++ tailWord_4390242).sum := by decide
  have hdescent : baseEnd_4390242 < baseStart_4390242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390311 : List Nat := [1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 7]
def baseStart_4390311 : Nat := 118140960795 + 4390311 * 2 ^ 59
def prefixEnd_4390311 : Nat := 4983230072969 + 3 ^ 40 * 4390311 * 2
def baseEnd_4390311 : Nat := 2254339765721477621721833

theorem tailTrace_4390311 : CollatzResearch.WordTrace tailWord_4390311 prefixEnd_4390311 2254339765721477621721833 := by
  unfold tailWord_4390311
  simp only [CollatzResearch.WordTrace]
  refine ⟨160127797197660527268850787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106751864798440351512567191 160127797197660527268850787)
  ·
    refine ⟨240191695796490790903276181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160127797197660527268850787 240191695796490790903276181)
    ·
      refine ⟨11258985740460505823591071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 240191695796490790903276181 11258985740460505823591071)
      ·
        refine ⟨16888478610690758735386607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11258985740460505823591071 16888478610690758735386607)
        ·
          refine ⟨25332717916036138103079911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16888478610690758735386607 25332717916036138103079911)
          ·
            refine ⟨37999076874054207154619867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25332717916036138103079911 37999076874054207154619867)
            ·
              refine ⟨56998615311081310731929801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37999076874054207154619867 56998615311081310731929801)
              ·
                refine ⟨42748961483310983048947351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56998615311081310731929801 42748961483310983048947351)
                ·
                  refine ⟨64123442224966474573421027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42748961483310983048947351 64123442224966474573421027)
                  ·
                    refine ⟨96185163337449711860131541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 64123442224966474573421027 96185163337449711860131541)
                    ·
                      refine ⟨2254339765721477621721833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 96185163337449711860131541 2254339765721477621721833)
                      ·
                        rfl

theorem cell23_4390311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_4390311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390311 prefixEnd_4390311 := by exact prefixLift 4390311
  have htrace : WordTrace (prefixWord ++ tailWord_4390311) baseStart_4390311 baseEnd_4390311 := by
    simpa [prefixWord, tailWord_4390311, baseEnd_4390311] using wordTrace_append hprefix tailTrace_4390311
  have hstable : (prefixWord ++ tailWord_4390311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390311).length < 2 ^ (prefixWord ++ tailWord_4390311).sum := by decide
  have hdescent : baseEnd_4390311 < baseStart_4390311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390365 : List Nat := [1, 4, 3, 1, 1, 3, 1, 2, 3, 4]
def baseStart_4390365 : Nat := 118140960795 + 4390365 * 2 ^ 59
def prefixEnd_4390365 : Nat := 4983230072969 + 3 ^ 40 * 4390365 * 2
def baseEnd_4390365 : Nat := 751455831225606803482195

theorem tailTrace_4390365 : CollatzResearch.WordTrace tailWord_4390365 prefixEnd_4390365 751455831225606803482195 := by
  unfold tailWord_4390365
  simp only [CollatzResearch.WordTrace]
  refine ⟨160129766739464894491316549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106753177826309929660877699 160129766739464894491316549)
  ·
    refine ⟨30024331263649667717121853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160129766739464894491316549 30024331263649667717121853)
    ·
      refine ⟨11259124223868625393920695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30024331263649667717121853 11259124223868625393920695)
      ·
        refine ⟨16888686335802938090881043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11259124223868625393920695 16888686335802938090881043)
        ·
          refine ⟨25333029503704407136321565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16888686335802938090881043 25333029503704407136321565)
          ·
            refine ⟨9499886063889152676120587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25333029503704407136321565 9499886063889152676120587)
            ·
              refine ⟨14249829095833729014180881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9499886063889152676120587 14249829095833729014180881)
              ·
                refine ⟨10687371821875296760635661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14249829095833729014180881 10687371821875296760635661)
                ·
                  refine ⟨4007764433203236285238373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10687371821875296760635661 4007764433203236285238373)
                  ·
                    refine ⟨751455831225606803482195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4007764433203236285238373 751455831225606803482195)
                    ·
                      rfl

theorem cell23_4390365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_4390365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390365 prefixEnd_4390365 := by exact prefixLift 4390365
  have htrace : WordTrace (prefixWord ++ tailWord_4390365) baseStart_4390365 baseEnd_4390365 := by
    simpa [prefixWord, tailWord_4390365, baseEnd_4390365] using wordTrace_append hprefix tailTrace_4390365
  have hstable : (prefixWord ++ tailWord_4390365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390365).length < 2 ^ (prefixWord ++ tailWord_4390365).sum := by decide
  have hdescent : baseEnd_4390365 < baseStart_4390365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390375 : List Nat := [1, 1, 5, 2, 1, 2, 3, 1, 2, 2, 3]
def baseStart_4390375 : Nat := 118140960795 + 4390375 * 2 ^ 59
def prefixEnd_4390375 : Nat := 4983230072969 + 3 ^ 40 * 4390375 * 2
def baseEnd_4390375 : Nat := 2254372628483365371321539

theorem tailTrace_4390375 : CollatzResearch.WordTrace tailWord_4390375 prefixEnd_4390375 2254372628483365371321539 := by
  unfold tailWord_4390375
  simp only [CollatzResearch.WordTrace]
  refine ⟨160130131469428666199180579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106753420979619110799453719 160130131469428666199180579)
  ·
    refine ⟨240195197204142999298770869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160130131469428666199180579 240195197204142999298770869)
    ·
      refine ⟨22518299737888406184259769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 240195197204142999298770869 22518299737888406184259769)
      ·
        refine ⟨16888724803416304638194827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22518299737888406184259769 16888724803416304638194827)
        ·
          refine ⟨25333087205124456957292241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16888724803416304638194827 25333087205124456957292241)
          ·
            refine ⟨18999815403843342717969181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25333087205124456957292241 18999815403843342717969181)
            ·
              refine ⟨7124930776441253519238443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18999815403843342717969181 7124930776441253519238443)
              ·
                refine ⟨10687396164661880278857665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7124930776441253519238443 10687396164661880278857665)
                ·
                  refine ⟨8015547123496410209143249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10687396164661880278857665 8015547123496410209143249)
                  ·
                    refine ⟨6011660342622307656857437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8015547123496410209143249 6011660342622307656857437)
                    ·
                      refine ⟨2254372628483365371321539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6011660342622307656857437 2254372628483365371321539)
                      ·
                        rfl

theorem cell23_4390375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_4390375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390375 prefixEnd_4390375 := by exact prefixLift 4390375
  have htrace : WordTrace (prefixWord ++ tailWord_4390375) baseStart_4390375 baseEnd_4390375 := by
    simpa [prefixWord, tailWord_4390375, baseEnd_4390375] using wordTrace_append hprefix tailTrace_4390375
  have hstable : (prefixWord ++ tailWord_4390375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390375).length < 2 ^ (prefixWord ++ tailWord_4390375).sum := by decide
  have hdescent : baseEnd_4390375 < baseStart_4390375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390382 : List Nat := [4, 1, 2, 1, 2, 1, 4, 3, 1, 4]
def baseStart_4390382 : Nat := 118140960795 + 4390382 * 2 ^ 59
def prefixEnd_4390382 : Nat := 4983230072969 + 3 ^ 40 * 4390382 * 2
def baseEnd_4390382 : Nat := 751458740949315614644669

theorem tailTrace_4390382 : CollatzResearch.WordTrace tailWord_4390382 prefixEnd_4390382 751458740949315614644669 := by
  unfold tailWord_4390382
  simp only [CollatzResearch.WordTrace]
  refine ⟨20016298347550413299335675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106753591186935537596456933 20016298347550413299335675)
  ·
    refine ⟨30024447521325619949003513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20016298347550413299335675 30024447521325619949003513)
    ·
      refine ⟨22518335640994214961752635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30024447521325619949003513 22518335640994214961752635)
      ·
        refine ⟨33777503461491322442628953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22518335640994214961752635 33777503461491322442628953)
        ·
          refine ⟨25333127596118491831971715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33777503461491322442628953 25333127596118491831971715)
          ·
            refine ⟨37999691394177737747957573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25333127596118491831971715 37999691394177737747957573)
            ·
              refine ⟨7124942136408325827742045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37999691394177737747957573 7124942136408325827742045)
              ·
                refine ⟨2671853301153122185403267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7124942136408325827742045 2671853301153122185403267)
                ·
                  refine ⟨4007779951729683278104901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2671853301153122185403267 4007779951729683278104901)
                  ·
                    refine ⟨751458740949315614644669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4007779951729683278104901 751458740949315614644669)
                    ·
                      rfl

theorem cell23_4390382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_4390382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390382 prefixEnd_4390382 := by exact prefixLift 4390382
  have htrace : WordTrace (prefixWord ++ tailWord_4390382) baseStart_4390382 baseEnd_4390382 := by
    simpa [prefixWord, tailWord_4390382, baseEnd_4390382] using wordTrace_append hprefix tailTrace_4390382
  have hstable : (prefixWord ++ tailWord_4390382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390382).length < 2 ^ (prefixWord ++ tailWord_4390382).sum := by decide
  have hdescent : baseEnd_4390382 < baseStart_4390382 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390391 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 5, 5]
def baseStart_4390391 : Nat := 118140960795 + 4390391 * 2 ^ 59
def prefixEnd_4390391 : Nat := 4983230072969 + 3 ^ 40 * 4390391 * 2
def baseEnd_4390391 : Nat := 751460281391279102907155

theorem tailTrace_4390391 : CollatzResearch.WordTrace tailWord_4390391 prefixEnd_4390391 751460281391279102907155 := by
  unfold tailWord_4390391
  simp only [CollatzResearch.WordTrace]
  refine ⟨160130715037370700931763027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106753810024913800621175351 160130715037370700931763027)
  ·
    refine ⟨240196072556056051397644541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160130715037370700931763027 240196072556056051397644541)
    ·
      refine ⟨90073527208521019274116703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 240196072556056051397644541 90073527208521019274116703)
      ·
        refine ⟨135110290812781528911175055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90073527208521019274116703 135110290812781528911175055)
        ·
          refine ⟨202665436219172293366762583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135110290812781528911175055 202665436219172293366762583)
          ·
            refine ⟨303998154328758440050143875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202665436219172293366762583 303998154328758440050143875)
            ·
              refine ⟨455997231493137660075215813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 303998154328758440050143875 455997231493137660075215813)
              ·
                refine ⟨85499480904963311264102965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 455997231493137660075215813 85499480904963311264102965)
                ·
                  refine ⟨8015576334840310431009653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 85499480904963311264102965 8015576334840310431009653)
                  ·
                    refine ⟨751460281391279102907155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8015576334840310431009653 751460281391279102907155)
                    ·
                      rfl

theorem cell23_4390391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 5, 5].length) (baseStart_4390391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390391 prefixEnd_4390391 := by exact prefixLift 4390391
  have htrace : WordTrace (prefixWord ++ tailWord_4390391) baseStart_4390391 baseEnd_4390391 := by
    simpa [prefixWord, tailWord_4390391, baseEnd_4390391] using wordTrace_append hprefix tailTrace_4390391
  have hstable : (prefixWord ++ tailWord_4390391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390391).length < 2 ^ (prefixWord ++ tailWord_4390391).sum := by decide
  have hdescent : baseEnd_4390391 < baseStart_4390391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390448 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 3]
def baseStart_4390448 : Nat := 118140960795 + 4390448 * 2 ^ 59
def prefixEnd_4390448 : Nat := 4983230072969 + 3 ^ 40 * 4390448 * 2
def baseEnd_4390448 : Nat := 2254410112571143585708703

theorem tailTrace_4390448 : CollatzResearch.WordTrace tailWord_4390448 prefixEnd_4390448 2254410112571143585708703 := by
  unfold tailWord_4390448
  simp only [CollatzResearch.WordTrace]
  refine ⟨80066396999082099833293999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106755195998776133111058665 80066396999082099833293999)
  ·
    refine ⟨120099595498623149749940999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80066396999082099833293999 120099595498623149749940999)
    ·
      refine ⟨180149393247934724624911499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120099595498623149749940999 180149393247934724624911499)
      ·
        refine ⟨270224089871902086937367249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180149393247934724624911499 270224089871902086937367249)
        ·
          refine ⟨202668067403926565203025437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 270224089871902086937367249 202668067403926565203025437)
          ·
            refine ⟨76000525276472461951134539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 202668067403926565203025437 76000525276472461951134539)
            ·
              refine ⟨114000787914708692926701809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76000525276472461951134539 114000787914708692926701809)
              ·
                refine ⟨85500590936031519695026357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114000787914708692926701809 85500590936031519695026357)
                ·
                  refine ⟨8015680400252954971408721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 85500590936031519695026357 8015680400252954971408721)
                  ·
                    refine ⟨6011760300189716228556541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8015680400252954971408721 6011760300189716228556541)
                    ·
                      refine ⟨2254410112571143585708703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6011760300189716228556541 2254410112571143585708703)
                      ·
                        rfl

theorem cell23_4390448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 3].length) (baseStart_4390448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390448 prefixEnd_4390448 := by exact prefixLift 4390448
  have htrace : WordTrace (prefixWord ++ tailWord_4390448) baseStart_4390448 baseEnd_4390448 := by
    simpa [prefixWord, tailWord_4390448, baseEnd_4390448] using wordTrace_append hprefix tailTrace_4390448
  have hstable : (prefixWord ++ tailWord_4390448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390448).length < 2 ^ (prefixWord ++ tailWord_4390448).sum := by decide
  have hdescent : baseEnd_4390448 < baseStart_4390448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390451 : List Nat := [1, 1, 1, 2, 4, 3, 11]
def baseStart_4390451 : Nat := 118140960795 + 4390451 * 2 ^ 59
def prefixEnd_4390451 : Nat := 4983230072969 + 3 ^ 40 * 4390451 * 2
def baseEnd_4390451 : Nat := 27832242629791445357669

theorem tailTrace_4390451 : CollatzResearch.WordTrace tailWord_4390451 prefixEnd_4390451 27832242629791445357669 := by
  unfold tailWord_4390451
  simp only [CollatzResearch.WordTrace]
  refine ⟨160132903417153331178947207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106755268944768887452631471 160132903417153331178947207)
  ·
    refine ⟨240199355125729996768420811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160132903417153331178947207 240199355125729996768420811)
    ·
      refine ⟨360299032688594995152631217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240199355125729996768420811 360299032688594995152631217)
      ·
        refine ⟨270224274516446246364473413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 360299032688594995152631217 270224274516446246364473413)
        ·
          refine ⟨50667051471833671193338765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 270224274516446246364473413 50667051471833671193338765)
          ·
            refine ⟨19000144301937626697502037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50667051471833671193338765 19000144301937626697502037)
            ·
              refine ⟨27832242629791445357669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 19000144301937626697502037 27832242629791445357669)
              ·
                rfl

theorem cell23_4390451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 11].length) (baseStart_4390451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390451 prefixEnd_4390451 := by exact prefixLift 4390451
  have htrace : WordTrace (prefixWord ++ tailWord_4390451) baseStart_4390451 baseEnd_4390451 := by
    simpa [prefixWord, tailWord_4390451, baseEnd_4390451] using wordTrace_append hprefix tailTrace_4390451
  have hstable : (prefixWord ++ tailWord_4390451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390451).length < 2 ^ (prefixWord ++ tailWord_4390451).sum := by decide
  have hdescent : baseEnd_4390451 < baseStart_4390451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390465 : List Nat := [1, 2, 5, 1, 1, 1, 2, 2, 3, 2, 3]
def baseStart_4390465 : Nat := 118140960795 + 4390465 * 2 ^ 59
def prefixEnd_4390465 : Nat := 4983230072969 + 3 ^ 40 * 4390465 * 2
def baseEnd_4390465 : Nat := 2254418841742270019196125

theorem tailTrace_4390465 : CollatzResearch.WordTrace tailWord_4390465 prefixEnd_4390465 2254418841742270019196125 := by
  unfold tailWord_4390465
  simp only [CollatzResearch.WordTrace]
  refine ⟨160133414039102611569956849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106755609359401741046637899 160133414039102611569956849)
  ·
    refine ⟨120100060529326958677467637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160133414039102611569956849 120100060529326958677467637)
    ·
      refine ⟨11259380674624402376012591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 120100060529326958677467637 11259380674624402376012591)
      ·
        refine ⟨16889071011936603564018887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11259380674624402376012591 16889071011936603564018887)
        ·
          refine ⟨25333606517904905346028331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16889071011936603564018887 25333606517904905346028331)
          ·
            refine ⟨38000409776857358019042497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25333606517904905346028331 38000409776857358019042497)
            ·
              refine ⟨28500307332643018514281873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38000409776857358019042497 28500307332643018514281873)
              ·
                refine ⟨21375230499482263885711405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28500307332643018514281873 21375230499482263885711405)
                ·
                  refine ⟨8015711437305848957141777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21375230499482263885711405 8015711437305848957141777)
                  ·
                    refine ⟨6011783577979386717856333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8015711437305848957141777 6011783577979386717856333)
                    ·
                      refine ⟨2254418841742270019196125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6011783577979386717856333 2254418841742270019196125)
                      ·
                        rfl

theorem cell23_4390465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_4390465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390465 prefixEnd_4390465 := by exact prefixLift 4390465
  have htrace : WordTrace (prefixWord ++ tailWord_4390465) baseStart_4390465 baseEnd_4390465 := by
    simpa [prefixWord, tailWord_4390465, baseEnd_4390465] using wordTrace_append hprefix tailTrace_4390465
  have hstable : (prefixWord ++ tailWord_4390465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390465).length < 2 ^ (prefixWord ++ tailWord_4390465).sum := by decide
  have hdescent : baseEnd_4390465 < baseStart_4390465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390482 : List Nat := [3, 2, 2, 1, 2, 2, 3, 2, 1, 2, 3]
def baseStart_4390482 : Nat := 118140960795 + 4390482 * 2 ^ 59
def prefixEnd_4390482 : Nat := 4983230072969 + 3 ^ 40 * 4390482 * 2
def baseEnd_4390482 : Nat := 2254427570913396452683547

theorem tailTrace_4390482 : CollatzResearch.WordTrace tailWord_4390482 prefixEnd_4390482 2254427570913396452683547 := by
  unfold tailWord_4390482
  simp only [CollatzResearch.WordTrace]
  refine ⟨40033508520010255868331425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106756022720027348982217133 40033508520010255868331425)
  ·
    refine ⟨30025131390007691901248569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40033508520010255868331425 30025131390007691901248569)
    ·
      refine ⟨22518848542505768925936427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30025131390007691901248569 22518848542505768925936427)
      ·
        refine ⟨33778272813758653388904641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22518848542505768925936427 33778272813758653388904641)
        ·
          refine ⟨25333704610318990041678481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33778272813758653388904641 25333704610318990041678481)
          ·
            refine ⟨19000278457739242531258861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25333704610318990041678481 19000278457739242531258861)
            ·
              refine ⟨7125104421652215949222073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19000278457739242531258861 7125104421652215949222073)
              ·
                refine ⟨5343828316239161961916555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7125104421652215949222073 5343828316239161961916555)
                ·
                  refine ⟨8015742474358742942874833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5343828316239161961916555 8015742474358742942874833)
                  ·
                    refine ⟨6011806855769057207156125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8015742474358742942874833 6011806855769057207156125)
                    ·
                      refine ⟨2254427570913396452683547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6011806855769057207156125 2254427570913396452683547)
                      ·
                        rfl

theorem cell23_4390482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_4390482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390482 prefixEnd_4390482 := by exact prefixLift 4390482
  have htrace : WordTrace (prefixWord ++ tailWord_4390482) baseStart_4390482 baseEnd_4390482 := by
    simpa [prefixWord, tailWord_4390482, baseEnd_4390482] using wordTrace_append hprefix tailTrace_4390482
  have hstable : (prefixWord ++ tailWord_4390482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390482).length < 2 ^ (prefixWord ++ tailWord_4390482).sum := by decide
  have hdescent : baseEnd_4390482 < baseStart_4390482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390512 : List Nat := [2, 1, 1, 1, 6, 1, 1, 4, 2, 1, 3]
def baseStart_4390512 : Nat := 118140960795 + 4390512 * 2 ^ 59
def prefixEnd_4390512 : Nat := 4983230072969 + 3 ^ 40 * 4390512 * 2
def baseEnd_4390512 : Nat := 2254442975333031335308409

theorem tailTrace_4390512 : CollatzResearch.WordTrace tailWord_4390512 prefixEnd_4390512 2254442975333031335308409 := by
  unfold tailWord_4390512
  simp only [CollatzResearch.WordTrace]
  refine ⟨80067564134966169298458895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106756752179954892397945193 80067564134966169298458895)
  ·
    refine ⟨120101346202449253947688343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80067564134966169298458895 120101346202449253947688343)
    ·
      refine ⟨180152019303673880921532515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120101346202449253947688343 180152019303673880921532515)
      ·
        refine ⟨270228028955510821382298773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180152019303673880921532515 270228028955510821382298773)
        ·
          refine ⟨12666938857289569752295255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 270228028955510821382298773 12666938857289569752295255)
          ·
            refine ⟨19000408285934354628442883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12666938857289569752295255 19000408285934354628442883)
            ·
              refine ⟨28500612428901531942664325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19000408285934354628442883 28500612428901531942664325)
              ·
                refine ⟨5343864830419037239249561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28500612428901531942664325 5343864830419037239249561)
                ·
                  refine ⟨4007898622814277929437171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5343864830419037239249561 4007898622814277929437171)
                  ·
                    refine ⟨6011847934221416894155757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4007898622814277929437171 6011847934221416894155757)
                    ·
                      refine ⟨2254442975333031335308409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6011847934221416894155757 2254442975333031335308409)
                      ·
                        rfl

theorem cell23_4390512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 2, 1, 3].length) (baseStart_4390512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390512 prefixEnd_4390512 := by exact prefixLift 4390512
  have htrace : WordTrace (prefixWord ++ tailWord_4390512) baseStart_4390512 baseEnd_4390512 := by
    simpa [prefixWord, tailWord_4390512, baseEnd_4390512] using wordTrace_append hprefix tailTrace_4390512
  have hstable : (prefixWord ++ tailWord_4390512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390512).length < 2 ^ (prefixWord ++ tailWord_4390512).sum := by decide
  have hdescent : baseEnd_4390512 < baseStart_4390512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390528 : List Nat := [2, 1, 1, 2, 1, 4, 3, 1, 2, 6]
def baseStart_4390528 : Nat := 118140960795 + 4390528 * 2 ^ 59
def prefixEnd_4390528 : Nat := 4983230072969 + 3 ^ 40 * 4390528 * 2
def baseEnd_4390528 : Nat := 751483730341167757569445

theorem tailTrace_4390528 : CollatzResearch.WordTrace tailWord_4390528 prefixEnd_4390528 751483730341167757569445 := by
  unfold tailWord_4390528
  simp only [CollatzResearch.WordTrace]
  refine ⟨80067855918937186664750119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106757141225249582219666825 80067855918937186664750119)
  ·
    refine ⟨120101783878405779997125179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80067855918937186664750119 120101783878405779997125179)
    ·
      refine ⟨180152675817608669995687769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120101783878405779997125179 180152675817608669995687769)
      ·
        refine ⟨135114506863206502496765827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180152675817608669995687769 135114506863206502496765827)
        ·
          refine ⟨202671760294809753745148741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135114506863206502496765827 202671760294809753745148741)
          ·
            refine ⟨38000955055276828827215389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 202671760294809753745148741 38000955055276828827215389)
            ·
              refine ⟨14250358145728810810205771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38000955055276828827215389 14250358145728810810205771)
              ·
                refine ⟨21375537218593216215308657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14250358145728810810205771 21375537218593216215308657)
                ·
                  refine ⟨16031652913944912161481493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21375537218593216215308657 16031652913944912161481493)
                  ·
                    refine ⟨751483730341167757569445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16031652913944912161481493 751483730341167757569445)
                    ·
                      rfl

theorem cell23_4390528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 2, 6].length) (baseStart_4390528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390528 prefixEnd_4390528 := by exact prefixLift 4390528
  have htrace : WordTrace (prefixWord ++ tailWord_4390528) baseStart_4390528 baseEnd_4390528 := by
    simpa [prefixWord, tailWord_4390528, baseEnd_4390528] using wordTrace_append hprefix tailTrace_4390528
  have hstable : (prefixWord ++ tailWord_4390528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390528).length < 2 ^ (prefixWord ++ tailWord_4390528).sum := by decide
  have hdescent : baseEnd_4390528 < baseStart_4390528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390552 : List Nat := [2, 1, 2, 4, 1, 2, 2, 2, 1, 4, 2]
def baseStart_4390552 : Nat := 118140960795 + 4390552 * 2 ^ 59
def prefixEnd_4390552 : Nat := 4983230072969 + 3 ^ 40 * 4390552 * 2
def baseEnd_4390552 : Nat := 2254463514559211178808225

theorem tailTrace_4390552 : CollatzResearch.WordTrace tailWord_4390552 prefixEnd_4390552 2254463514559211178808225 := by
  unfold tailWord_4390552
  simp only [CollatzResearch.WordTrace]
  refine ⟨80068293594893712714186955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106757724793191616952249273 80068293594893712714186955)
  ·
    refine ⟨120102440392340569071280433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80068293594893712714186955 120102440392340569071280433)
    ·
      refine ⟨90076830294255426803460325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120102440392340569071280433 90076830294255426803460325)
      ·
        refine ⟨16889405680172892525648811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90076830294255426803460325 16889405680172892525648811)
        ·
          refine ⟨25334108520259338788473217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16889405680172892525648811 25334108520259338788473217)
          ·
            refine ⟨19000581390194504091354913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25334108520259338788473217 19000581390194504091354913)
            ·
              refine ⟨14250436042645878068516185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19000581390194504091354913 14250436042645878068516185)
              ·
                refine ⟨10687827031984408551387139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14250436042645878068516185 10687827031984408551387139)
                ·
                  refine ⟨16031740547976612827080709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10687827031984408551387139 16031740547976612827080709)
                  ·
                    refine ⟨3005951352745614905077633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16031740547976612827080709 3005951352745614905077633)
                    ·
                      refine ⟨2254463514559211178808225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3005951352745614905077633 2254463514559211178808225)
                      ·
                        rfl

theorem cell23_4390552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_4390552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390552 prefixEnd_4390552 := by exact prefixLift 4390552
  have htrace : WordTrace (prefixWord ++ tailWord_4390552) baseStart_4390552 baseEnd_4390552 := by
    simpa [prefixWord, tailWord_4390552, baseEnd_4390552] using wordTrace_append hprefix tailTrace_4390552
  have hstable : (prefixWord ++ tailWord_4390552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390552).length < 2 ^ (prefixWord ++ tailWord_4390552).sum := by decide
  have hdescent : baseEnd_4390552 < baseStart_4390552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390575 : List Nat := [1, 1, 2, 1, 2, 4, 1, 6, 5]
def baseStart_4390575 : Nat := 118140960795 + 4390575 * 2 ^ 59
def prefixEnd_4390575 : Nat := 4983230072969 + 3 ^ 40 * 4390575 * 2
def baseEnd_4390575 : Nat := 250497258290473843202291

theorem tailTrace_4390575 : CollatzResearch.WordTrace tailWord_4390575 prefixEnd_4390575 250497258290473843202291 := by
  unfold tailWord_4390575
  simp only [CollatzResearch.WordTrace]
  refine ⟨160137426068704100356461179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106758284045802733570974119 160137426068704100356461179)
  ·
    refine ⟨240206139103056150534691769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160137426068704100356461179 240206139103056150534691769)
    ·
      refine ⟨180154604327292112901018827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240206139103056150534691769 180154604327292112901018827)
      ·
        refine ⟨270231906490938169351528241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180154604327292112901018827 270231906490938169351528241)
        ·
          refine ⟨202673929868203627013646181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 270231906490938169351528241 202673929868203627013646181)
          ·
            refine ⟨38001361850288180065058659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 202673929868203627013646181 38001361850288180065058659)
            ·
              refine ⟨57002042775432270097587989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38001361850288180065058659 57002042775432270097587989)
              ·
                refine ⟨2671970755098387660824437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 57002042775432270097587989 2671970755098387660824437)
                ·
                  refine ⟨250497258290473843202291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2671970755098387660824437 250497258290473843202291)
                  ·
                    rfl

theorem cell23_4390575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 6, 5].length) (baseStart_4390575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390575 prefixEnd_4390575 := by exact prefixLift 4390575
  have htrace : WordTrace (prefixWord ++ tailWord_4390575) baseStart_4390575 baseEnd_4390575 := by
    simpa [prefixWord, tailWord_4390575, baseEnd_4390575] using wordTrace_append hprefix tailTrace_4390575
  have hstable : (prefixWord ++ tailWord_4390575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390575).length < 2 ^ (prefixWord ++ tailWord_4390575).sum := by decide
  have hdescent : baseEnd_4390575 < baseStart_4390575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390585 : List Nat := [1, 2, 1, 4, 1, 1, 4, 1, 2, 3, 3]
def baseStart_4390585 : Nat := 118140960795 + 4390585 * 2 ^ 59
def prefixEnd_4390585 : Nat := 4983230072969 + 3 ^ 40 * 4390585 * 2
def baseEnd_4390585 : Nat := 2254480459420809549695573

theorem tailTrace_4390585 : CollatzResearch.WordTrace tailWord_4390585 prefixEnd_4390585 2254480459420809549695573 := by
  unfold tailWord_4390585
  simp only [CollatzResearch.WordTrace]
  refine ⟨160137790798667872064325209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106758527199111914709550139 160137790798667872064325209)
  ·
    refine ⟨120103343099000904048243907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160137790798667872064325209 120103343099000904048243907)
    ·
      refine ⟨180155014648501356072365861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120103343099000904048243907 180155014648501356072365861)
      ·
        refine ⟨33779065246594004263568599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 180155014648501356072365861 33779065246594004263568599)
        ·
          refine ⟨50668597869891006395352899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33779065246594004263568599 50668597869891006395352899)
          ·
            refine ⟨76002896804836509593029349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50668597869891006395352899 76002896804836509593029349)
            ·
              refine ⟨14250543150906845548693003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76002896804836509593029349 14250543150906845548693003)
              ·
                refine ⟨21375814726360268323039505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14250543150906845548693003 21375814726360268323039505)
                ·
                  refine ⟨16031861044770201242279629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21375814726360268323039505 16031861044770201242279629)
                  ·
                    refine ⟨6011947891788825465854861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16031861044770201242279629 6011947891788825465854861)
                    ·
                      refine ⟨2254480459420809549695573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6011947891788825465854861 2254480459420809549695573)
                      ·
                        rfl

theorem cell23_4390585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_4390585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390585 prefixEnd_4390585 := by exact prefixLift 4390585
  have htrace : WordTrace (prefixWord ++ tailWord_4390585) baseStart_4390585 baseEnd_4390585 := by
    simpa [prefixWord, tailWord_4390585, baseEnd_4390585] using wordTrace_append hprefix tailTrace_4390585
  have hstable : (prefixWord ++ tailWord_4390585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390585).length < 2 ^ (prefixWord ++ tailWord_4390585).sum := by decide
  have hdescent : baseEnd_4390585 < baseStart_4390585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390586 : List Nat := [3, 1, 1, 1, 2, 5, 3, 1, 2, 2, 2]
def baseStart_4390586 : Nat := 118140960795 + 4390586 * 2 ^ 59
def prefixEnd_4390586 : Nat := 4983230072969 + 3 ^ 40 * 4390586 * 2
def baseEnd_4390586 : Nat := 2254480972901464045783069

theorem tailTrace_4390586 : CollatzResearch.WordTrace tailWord_4390586 prefixEnd_4390586 2254480972901464045783069 := by
  unfold tailWord_4390586
  simp only [CollatzResearch.WordTrace]
  refine ⟨40034456817916062308777903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106758551514442832823407741 40034456817916062308777903)
  ·
    refine ⟨60051685226874093463166855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40034456817916062308777903 60051685226874093463166855)
    ·
      refine ⟨90077527840311140194750283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60051685226874093463166855 90077527840311140194750283)
      ·
        refine ⟨135116291760466710292125425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90077527840311140194750283 135116291760466710292125425)
        ·
          refine ⟨101337218820350032719094069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135116291760466710292125425 101337218820350032719094069)
          ·
            refine ⟨9500364264407815567415069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 101337218820350032719094069 9500364264407815567415069)
            ·
              refine ⟨3562636599152930837780651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9500364264407815567415069 3562636599152930837780651)
              ·
                refine ⟨5343954898729396256670977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3562636599152930837780651 5343954898729396256670977)
                ·
                  refine ⟨4007966174047047192503233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5343954898729396256670977 4007966174047047192503233)
                  ·
                    refine ⟨3005974630535285394377425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4007966174047047192503233 3005974630535285394377425)
                    ·
                      refine ⟨2254480972901464045783069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3005974630535285394377425 2254480972901464045783069)
                      ·
                        rfl

theorem cell23_4390586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 1, 2, 2, 2].length) (baseStart_4390586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390586 prefixEnd_4390586 := by exact prefixLift 4390586
  have htrace : WordTrace (prefixWord ++ tailWord_4390586) baseStart_4390586 baseEnd_4390586 := by
    simpa [prefixWord, tailWord_4390586, baseEnd_4390586] using wordTrace_append hprefix tailTrace_4390586
  have hstable : (prefixWord ++ tailWord_4390586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390586).length < 2 ^ (prefixWord ++ tailWord_4390586).sum := by decide
  have hdescent : baseEnd_4390586 < baseStart_4390586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390642 : List Nat := [3, 2, 1, 3, 1, 1, 2, 1, 1, 6, 2]
def baseStart_4390642 : Nat := 118140960795 + 4390642 * 2 ^ 59
def prefixEnd_4390642 : Nat := 4983230072969 + 3 ^ 40 * 4390642 * 2
def baseEnd_4390642 : Nat := 2254509727818115826682811

theorem tailTrace_4390642 : CollatzResearch.WordTrace tailWord_4390642 prefixEnd_4390642 2254509727818115826682811 := by
  unfold tailWord_4390642
  simp only [CollatzResearch.WordTrace]
  refine ⟨40034967439865342699787545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106759913172974247199433453 40034967439865342699787545)
  ·
    refine ⟨30026225579899007024840659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40034967439865342699787545 30026225579899007024840659)
    ·
      refine ⟨45039338369848510537260989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30026225579899007024840659 45039338369848510537260989)
      ·
        refine ⟨16889751888693191451472871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45039338369848510537260989 16889751888693191451472871)
        ·
          refine ⟨25334627833039787177209307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16889751888693191451472871 25334627833039787177209307)
          ·
            refine ⟨38001941749559680765813961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25334627833039787177209307 38001941749559680765813961)
            ·
              refine ⟨28501456312169760574360471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38001941749559680765813961 28501456312169760574360471)
              ·
                refine ⟨42752184468254640861540707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28501456312169760574360471 42752184468254640861540707)
                ·
                  refine ⟨64128276702381961292311061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42752184468254640861540707 64128276702381961292311061)
                  ·
                    refine ⟨3006012970424154435577081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 64128276702381961292311061 3006012970424154435577081)
                    ·
                      refine ⟨2254509727818115826682811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3006012970424154435577081 2254509727818115826682811)
                      ·
                        rfl

theorem cell23_4390642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_4390642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390642 prefixEnd_4390642 := by exact prefixLift 4390642
  have htrace : WordTrace (prefixWord ++ tailWord_4390642) baseStart_4390642 baseEnd_4390642 := by
    simpa [prefixWord, tailWord_4390642, baseEnd_4390642] using wordTrace_append hprefix tailTrace_4390642
  have hstable : (prefixWord ++ tailWord_4390642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390642).length < 2 ^ (prefixWord ++ tailWord_4390642).sum := by decide
  have hdescent : baseEnd_4390642 < baseStart_4390642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390648 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 10]
def baseStart_4390648 : Nat := 118140960795 + 4390648 * 2 ^ 59
def prefixEnd_4390648 : Nat := 4983230072969 + 3 ^ 40 * 4390648 * 2
def baseEnd_4390648 : Nat := 250501423189115867023087

theorem tailTrace_4390648 : CollatzResearch.WordTrace tailWord_4390648 prefixEnd_4390648 250501423189115867023087 := by
  unfold tailWord_4390648
  simp only [CollatzResearch.WordTrace]
  refine ⟨80070044298719816911934299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106760059064959755882579065 80070044298719816911934299)
  ·
    refine ⟨120105066448079725367901449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80070044298719816911934299 120105066448079725367901449)
    ·
      refine ⟨90078799836059794025926087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120105066448079725367901449 90078799836059794025926087)
      ·
        refine ⟨135118199754089691038889131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90078799836059794025926087 135118199754089691038889131)
        ·
          refine ⟨202677299631134536558333697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135118199754089691038889131 202677299631134536558333697)
          ·
            refine ⟨152007974723350902418750273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202677299631134536558333697 152007974723350902418750273)
            ·
              refine ⟨114005981042513176814062705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152007974723350902418750273 114005981042513176814062705)
              ·
                refine ⟨85504485781884882610547029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114005981042513176814062705 85504485781884882610547029)
                ·
                  refine ⟨250501423189115867023087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 85504485781884882610547029 250501423189115867023087)
                  ·
                    rfl

theorem cell23_4390648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 10].length) (baseStart_4390648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390648 prefixEnd_4390648 := by exact prefixLift 4390648
  have htrace : WordTrace (prefixWord ++ tailWord_4390648) baseStart_4390648 baseEnd_4390648 := by
    simpa [prefixWord, tailWord_4390648, baseEnd_4390648] using wordTrace_append hprefix tailTrace_4390648
  have hstable : (prefixWord ++ tailWord_4390648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390648).length < 2 ^ (prefixWord ++ tailWord_4390648).sum := by decide
  have hdescent : baseEnd_4390648 < baseStart_4390648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390682 : List Nat := [3, 1, 1, 3, 2, 3, 2, 2, 6]
def baseStart_4390682 : Nat := 118140960795 + 4390682 * 2 ^ 59
def prefixEnd_4390682 : Nat := 4983230072969 + 3 ^ 40 * 4390682 * 2
def baseEnd_4390682 : Nat := 250503363004921741131403

theorem tailTrace_4390682 : CollatzResearch.WordTrace tailWord_4390682 prefixEnd_4390682 250503363004921741131403 := by
  unfold tailWord_4390682
  simp only [CollatzResearch.WordTrace]
  refine ⟨40035332169829114407651575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106760885786210971753737533 40035332169829114407651575)
  ·
    refine ⟨60052998254743671611477363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40035332169829114407651575 60052998254743671611477363)
    ·
      refine ⟨90079497382115507417216045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60052998254743671611477363 90079497382115507417216045)
      ·
        refine ⟨33779811518293315281456017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90079497382115507417216045 33779811518293315281456017)
        ·
          refine ⟨25334858638719986461092013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33779811518293315281456017 25334858638719986461092013)
          ·
            refine ⟨9500571989519994922909505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25334858638719986461092013 9500571989519994922909505)
            ·
              refine ⟨7125428992139996192182129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9500571989519994922909505 7125428992139996192182129)
              ·
                refine ⟨5344071744104997144136597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7125428992139996192182129 5344071744104997144136597)
                ·
                  refine ⟨250503363004921741131403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5344071744104997144136597 250503363004921741131403)
                  ·
                    rfl

theorem cell23_4390682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 6].length) (baseStart_4390682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390682 prefixEnd_4390682 := by exact prefixLift 4390682
  have htrace : WordTrace (prefixWord ++ tailWord_4390682) baseStart_4390682 baseEnd_4390682 := by
    simpa [prefixWord, tailWord_4390682, baseEnd_4390682] using wordTrace_append hprefix tailTrace_4390682
  have hstable : (prefixWord ++ tailWord_4390682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390682).length < 2 ^ (prefixWord ++ tailWord_4390682).sum := by decide
  have hdescent : baseEnd_4390682 < baseStart_4390682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390713 : List Nat := [1, 2, 1, 7, 2, 1, 1, 1, 2, 2, 3]
def baseStart_4390713 : Nat := 118140960795 + 4390713 * 2 ^ 59
def prefixEnd_4390713 : Nat := 4983230072969 + 3 ^ 40 * 4390713 * 2
def baseEnd_4390713 : Nat := 2254546184944585048894985

theorem tailTrace_4390713 : CollatzResearch.WordTrace tailWord_4390713 prefixEnd_4390713 2254546184944585048894985 := by
  unfold tailWord_4390713
  simp only [CollatzResearch.WordTrace]
  refine ⟨160142459342204149924984793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106761639561469433283323195 160142459342204149924984793)
  ·
    refine ⟨120106844506653112443738595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160142459342204149924984793 120106844506653112443738595)
    ·
      refine ⟨180160266759979668665607893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120106844506653112443738595 180160266759979668665607893)
      ·
        refine ⟨4222506252187023484350185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 180160266759979668665607893 4222506252187023484350185)
        ·
          refine ⟨3166879689140267613262639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4222506252187023484350185 3166879689140267613262639)
          ·
            refine ⟨4750319533710401419893959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3166879689140267613262639 4750319533710401419893959)
            ·
              refine ⟨7125479300565602129840939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4750319533710401419893959 7125479300565602129840939)
              ·
                refine ⟨10688218950848403194761409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7125479300565602129840939 10688218950848403194761409)
                ·
                  refine ⟨8016164213136302396071057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10688218950848403194761409 8016164213136302396071057)
                  ·
                    refine ⟨6012123159852226797053293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8016164213136302396071057 6012123159852226797053293)
                    ·
                      refine ⟨2254546184944585048894985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6012123159852226797053293 2254546184944585048894985)
                      ·
                        rfl

theorem cell23_4390713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_4390713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390713 prefixEnd_4390713 := by exact prefixLift 4390713
  have htrace : WordTrace (prefixWord ++ tailWord_4390713) baseStart_4390713 baseEnd_4390713 := by
    simpa [prefixWord, tailWord_4390713, baseEnd_4390713] using wordTrace_append hprefix tailTrace_4390713
  have hstable : (prefixWord ++ tailWord_4390713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390713).length < 2 ^ (prefixWord ++ tailWord_4390713).sum := by decide
  have hdescent : baseEnd_4390713 < baseStart_4390713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390719 : List Nat := [1, 1, 2, 2, 6, 1, 1, 1, 1, 5, 2]
def baseStart_4390719 : Nat := 118140960795 + 4390719 * 2 ^ 59
def prefixEnd_4390719 : Nat := 4983230072969 + 3 ^ 40 * 4390719 * 2
def baseEnd_4390719 : Nat := 2254549265828512025419957

theorem tailTrace_4390719 : CollatzResearch.WordTrace tailWord_4390719 prefixEnd_4390719 2254549265828512025419957 := by
  unfold tailWord_4390719
  simp only [CollatzResearch.WordTrace]
  refine ⟨160142678180182412949703211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106761785453454941966468807 160142678180182412949703211)
  ·
    refine ⟨240214017270273619424554817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160142678180182412949703211 240214017270273619424554817)
    ·
      refine ⟨180160512952705214568416113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240214017270273619424554817 180160512952705214568416113)
      ·
        refine ⟨135120384714528910926312085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180160512952705214568416113 135120384714528910926312085)
        ·
          refine ⟨6333768033493542699670879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 135120384714528910926312085 6333768033493542699670879)
          ·
            refine ⟨9500652050240314049506319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6333768033493542699670879 9500652050240314049506319)
            ·
              refine ⟨14250978075360471074259479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9500652050240314049506319 14250978075360471074259479)
              ·
                refine ⟨21376467113040706611389219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14250978075360471074259479 21376467113040706611389219)
                ·
                  refine ⟨32064700669561059917083829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21376467113040706611389219 32064700669561059917083829)
                  ·
                    refine ⟨3006065687771349367226609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32064700669561059917083829 3006065687771349367226609)
                    ·
                      refine ⟨2254549265828512025419957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3006065687771349367226609 2254549265828512025419957)
                      ·
                        rfl

theorem cell23_4390719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 5, 2].length) (baseStart_4390719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390719 prefixEnd_4390719 := by exact prefixLift 4390719
  have htrace : WordTrace (prefixWord ++ tailWord_4390719) baseStart_4390719 baseEnd_4390719 := by
    simpa [prefixWord, tailWord_4390719, baseEnd_4390719] using wordTrace_append hprefix tailTrace_4390719
  have hstable : (prefixWord ++ tailWord_4390719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390719).length < 2 ^ (prefixWord ++ tailWord_4390719).sum := by decide
  have hdescent : baseEnd_4390719 < baseStart_4390719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390725 : List Nat := [1, 3, 1, 1, 1, 2, 3, 4, 1, 6]
def baseStart_4390725 : Nat := 118140960795 + 4390725 * 2 ^ 59
def prefixEnd_4390725 : Nat := 4983230072969 + 3 ^ 40 * 4390725 * 2
def baseEnd_4390725 : Nat := 751517448904146333981643

theorem tailTrace_4390725 : CollatzResearch.WordTrace tailWord_4390725 prefixEnd_4390725 751517448904146333981643 := by
  unfold tailWord_4390725
  simp only [CollatzResearch.WordTrace]
  refine ⟨160142897018160675974421629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106761931345440450649614419 160142897018160675974421629)
  ·
    refine ⟨60053586381810253490408111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160142897018160675974421629 60053586381810253490408111)
    ·
      refine ⟨90080379572715380235612167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60053586381810253490408111 90080379572715380235612167)
      ·
        refine ⟨135120569359073070353418251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90080379572715380235612167 135120569359073070353418251)
        ·
          refine ⟨202680854038609605530127377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135120569359073070353418251 202680854038609605530127377)
          ·
            refine ⟨152010640528957204147595533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202680854038609605530127377 152010640528957204147595533)
            ·
              refine ⟨57003990198358951555348325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 152010640528957204147595533 57003990198358951555348325)
              ·
                refine ⟨10688248162192303416627811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57003990198358951555348325 10688248162192303416627811)
                ·
                  refine ⟨16032372243288455124941717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10688248162192303416627811 16032372243288455124941717)
                  ·
                    refine ⟨751517448904146333981643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16032372243288455124941717 751517448904146333981643)
                    ·
                      rfl

theorem cell23_4390725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 1, 6].length) (baseStart_4390725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390725 prefixEnd_4390725 := by exact prefixLift 4390725
  have htrace : WordTrace (prefixWord ++ tailWord_4390725) baseStart_4390725 baseEnd_4390725 := by
    simpa [prefixWord, tailWord_4390725, baseEnd_4390725] using wordTrace_append hprefix tailTrace_4390725
  have hstable : (prefixWord ++ tailWord_4390725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390725).length < 2 ^ (prefixWord ++ tailWord_4390725).sum := by decide
  have hdescent : baseEnd_4390725 < baseStart_4390725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390745 : List Nat := [1, 2, 1, 2, 2, 3, 2, 2, 1, 1, 6]
def baseStart_4390745 : Nat := 118140960795 + 4390745 * 2 ^ 59
def prefixEnd_4390745 : Nat := 4983230072969 + 3 ^ 40 * 4390745 * 2
def baseEnd_4390745 : Nat := 2254562616325528923694837

theorem tailTrace_4390745 : CollatzResearch.WordTrace tailWord_4390745 prefixEnd_4390745 2254562616325528923694837 := by
  unfold tailWord_4390745
  simp only [CollatzResearch.WordTrace]
  refine ⟨160143626478088219390149689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106762417652058812926766459 160143626478088219390149689)
  ·
    refine ⟨120107719858566164542612267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160143626478088219390149689 120107719858566164542612267)
    ·
      refine ⟨180161579787849246813918401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120107719858566164542612267 180161579787849246813918401)
      ·
        refine ⟨135121184840886935110438801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180161579787849246813918401 135121184840886935110438801)
        ·
          refine ⟨101340888630665201332829101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135121184840886935110438801 101340888630665201332829101)
          ·
            refine ⟨38002833236499450499810913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101340888630665201332829101 38002833236499450499810913)
            ·
              refine ⟨28502124927374587874858185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38002833236499450499810913 28502124927374587874858185)
              ·
                refine ⟨21376593695530940906143639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28502124927374587874858185 21376593695530940906143639)
                ·
                  refine ⟨32064890543296411359215459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21376593695530940906143639 32064890543296411359215459)
                  ·
                    refine ⟨48097335814944617038823189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32064890543296411359215459 48097335814944617038823189)
                    ·
                      refine ⟨2254562616325528923694837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48097335814944617038823189 2254562616325528923694837)
                      ·
                        rfl

theorem cell23_4390745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 1, 6].length) (baseStart_4390745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390745 prefixEnd_4390745 := by exact prefixLift 4390745
  have htrace : WordTrace (prefixWord ++ tailWord_4390745) baseStart_4390745 baseEnd_4390745 := by
    simpa [prefixWord, tailWord_4390745, baseEnd_4390745] using wordTrace_append hprefix tailTrace_4390745
  have hstable : (prefixWord ++ tailWord_4390745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390745).length < 2 ^ (prefixWord ++ tailWord_4390745).sum := by decide
  have hdescent : baseEnd_4390745 < baseStart_4390745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390752 : List Nat := [2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 5]
def baseStart_4390752 : Nat := 118140960795 + 4390752 * 2 ^ 59
def prefixEnd_4390752 : Nat := 4983230072969 + 3 ^ 40 * 4390752 * 2
def baseEnd_4390752 : Nat := 2254566210690110396307305

theorem tailTrace_4390752 : CollatzResearch.WordTrace tailWord_4390752 prefixEnd_4390752 2254566210690110396307305 := by
  unfold tailWord_4390752
  simp only [CollatzResearch.WordTrace]
  refine ⟨80071940894531429792827255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106762587859375239723769673 80071940894531429792827255)
  ·
    refine ⟨120107911341797144689240883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80071940894531429792827255 120107911341797144689240883)
    ·
      refine ⟨180161867012695717033861325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120107911341797144689240883 180161867012695717033861325)
      ·
        refine ⟨67560700129760893887697997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 180161867012695717033861325 67560700129760893887697997)
        ·
          refine ⟨25335262548660335207886749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67560700129760893887697997 25335262548660335207886749)
          ·
            refine ⟨9500723455747625702957531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25335262548660335207886749 9500723455747625702957531)
            ·
              refine ⟨14251085183621438554436297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9500723455747625702957531 14251085183621438554436297)
              ·
                refine ⟨10688313887716078915827223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14251085183621438554436297 10688313887716078915827223)
                ·
                  refine ⟨16032470831574118373740835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10688313887716078915827223 16032470831574118373740835)
                  ·
                    refine ⟨24048706247361177560611253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16032470831574118373740835 24048706247361177560611253)
                    ·
                      refine ⟨2254566210690110396307305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24048706247361177560611253 2254566210690110396307305)
                      ·
                        rfl

theorem cell23_4390752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_4390752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390752 prefixEnd_4390752 := by exact prefixLift 4390752
  have htrace : WordTrace (prefixWord ++ tailWord_4390752) baseStart_4390752 baseEnd_4390752 := by
    simpa [prefixWord, tailWord_4390752, baseEnd_4390752] using wordTrace_append hprefix tailTrace_4390752
  have hstable : (prefixWord ++ tailWord_4390752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390752).length < 2 ^ (prefixWord ++ tailWord_4390752).sum := by decide
  have hdescent : baseEnd_4390752 < baseStart_4390752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390766 : List Nat := [4, 1, 2, 3, 1, 2, 2, 2, 1, 1, 4]
def baseStart_4390766 : Nat := 118140960795 + 4390766 * 2 ^ 59
def prefixEnd_4390766 : Nat := 4983230072969 + 3 ^ 40 * 4390766 * 2
def baseEnd_4390766 : Nat := 2254573399419273341532241

theorem tailTrace_4390766 : CollatzResearch.WordTrace tailWord_4390766 prefixEnd_4390766 2254573399419273341532241 := by
  unfold tailWord_4390766
  simp only [CollatzResearch.WordTrace]
  refine ⟨20018049051376517497083019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106762928274008093317776101 20018049051376517497083019)
  ·
    refine ⟨30027073577064776245624529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20018049051376517497083019 30027073577064776245624529)
    ·
      refine ⟨22520305182798582184218397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30027073577064776245624529 22520305182798582184218397)
      ·
        refine ⟨8445114443549468319081899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22520305182798582184218397 8445114443549468319081899)
        ·
          refine ⟨12667671665324202478622849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8445114443549468319081899 12667671665324202478622849)
          ·
            refine ⟨9500753748993151858967137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12667671665324202478622849 9500753748993151858967137)
            ·
              refine ⟨7125565311744863894225353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9500753748993151858967137 7125565311744863894225353)
              ·
                refine ⟨5344173983808647920669015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7125565311744863894225353 5344173983808647920669015)
                ·
                  refine ⟨8016260975712971881003523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5344173983808647920669015 8016260975712971881003523)
                  ·
                    refine ⟨12024391463569457821505285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8016260975712971881003523 12024391463569457821505285)
                    ·
                      refine ⟨2254573399419273341532241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12024391463569457821505285 2254573399419273341532241)
                      ·
                        rfl

theorem cell23_4390766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_4390766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390766 prefixEnd_4390766 := by exact prefixLift 4390766
  have htrace : WordTrace (prefixWord ++ tailWord_4390766) baseStart_4390766 baseEnd_4390766 := by
    simpa [prefixWord, tailWord_4390766, baseEnd_4390766] using wordTrace_append hprefix tailTrace_4390766
  have hstable : (prefixWord ++ tailWord_4390766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390766).length < 2 ^ (prefixWord ++ tailWord_4390766).sum := by decide
  have hdescent : baseEnd_4390766 < baseStart_4390766 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390769 : List Nat := [1, 2, 2, 2, 1, 3, 4, 2, 1, 2, 3]
def baseStart_4390769 : Nat := 118140960795 + 4390769 * 2 ^ 59
def prefixEnd_4390769 : Nat := 4983230072969 + 3 ^ 40 * 4390769 * 2
def baseEnd_4390769 : Nat := 2254574939861236829794727

theorem tailTrace_4390769 : CollatzResearch.WordTrace tailWord_4390769 prefixEnd_4390769 2254574939861236829794727 := by
  unfold tailWord_4390769
  simp only [CollatzResearch.WordTrace]
  refine ⟨160144501830001271489023361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106763001220000847659348907 160144501830001271489023361)
  ·
    refine ⟨120108376372500953616767521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160144501830001271489023361 120108376372500953616767521)
    ·
      refine ⟨90081282279375715212575641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120108376372500953616767521 90081282279375715212575641)
      ·
        refine ⟨67560961709531786409431731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90081282279375715212575641 67560961709531786409431731)
        ·
          refine ⟨101341442564297679614147597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67560961709531786409431731 101341442564297679614147597)
          ·
            refine ⟨38003040961611629855305349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101341442564297679614147597 38003040961611629855305349)
            ·
              refine ⟨7125570180302180597869753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38003040961611629855305349 7125570180302180597869753)
              ·
                refine ⟨5344177635226635448402315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7125570180302180597869753 5344177635226635448402315)
                ·
                  refine ⟨8016266452839953172603473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5344177635226635448402315 8016266452839953172603473)
                  ·
                    refine ⟨6012199839629964879452605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8016266452839953172603473 6012199839629964879452605)
                    ·
                      refine ⟨2254574939861236829794727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6012199839629964879452605 2254574939861236829794727)
                      ·
                        rfl

theorem cell23_4390769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 1, 2, 3].length) (baseStart_4390769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390769 prefixEnd_4390769 := by exact prefixLift 4390769
  have htrace : WordTrace (prefixWord ++ tailWord_4390769) baseStart_4390769 baseEnd_4390769 := by
    simpa [prefixWord, tailWord_4390769, baseEnd_4390769] using wordTrace_append hprefix tailTrace_4390769
  have hstable : (prefixWord ++ tailWord_4390769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390769).length < 2 ^ (prefixWord ++ tailWord_4390769).sum := by decide
  have hdescent : baseEnd_4390769 < baseStart_4390769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390795 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 5]
def baseStart_4390795 : Nat := 118140960795 + 4390795 * 2 ^ 59
def prefixEnd_4390795 : Nat := 4983230072969 + 3 ^ 40 * 4390795 * 2
def baseEnd_4390795 : Nat := 2254588290358253728069607

theorem tailTrace_4390795 : CollatzResearch.WordTrace tailWord_4390795 prefixEnd_4390795 2254588290358253728069607 := by
  unfold tailWord_4390795
  simp only [CollatzResearch.WordTrace]
  refine ⟨160145450127907077929469839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106763633418604718619646559 160145450127907077929469839)
  ·
    refine ⟨240218175191860616894204759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160145450127907077929469839 240218175191860616894204759)
    ·
      refine ⟨360327262787790925341307139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240218175191860616894204759 360327262787790925341307139)
      ·
        refine ⟨540490894181686388011960709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 360327262787790925341307139 540490894181686388011960709)
        ·
          refine ⟨101342042659066197752242633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 540490894181686388011960709 101342042659066197752242633)
          ·
            refine ⟨76006531994299648314181975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101342042659066197752242633 76006531994299648314181975)
            ·
              refine ⟨114009797991449472471272963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76006531994299648314181975 114009797991449472471272963)
              ·
                refine ⟨171014696987174208706909445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114009797991449472471272963 171014696987174208706909445)
                ·
                  refine ⟨32065255685095164132545521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 171014696987174208706909445 32065255685095164132545521)
                  ·
                    refine ⟨24048941763821373099409141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32065255685095164132545521 24048941763821373099409141)
                    ·
                      refine ⟨2254588290358253728069607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24048941763821373099409141 2254588290358253728069607)
                      ·
                        rfl

theorem cell23_4390795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 5].length) (baseStart_4390795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390795 prefixEnd_4390795 := by exact prefixLift 4390795
  have htrace : WordTrace (prefixWord ++ tailWord_4390795) baseStart_4390795 baseEnd_4390795 := by
    simpa [prefixWord, tailWord_4390795, baseEnd_4390795] using wordTrace_append hprefix tailTrace_4390795
  have hstable : (prefixWord ++ tailWord_4390795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390795).length < 2 ^ (prefixWord ++ tailWord_4390795).sum := by decide
  have hdescent : baseEnd_4390795 < baseStart_4390795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390862 : List Nat := [4, 1, 1, 1, 2, 2, 2, 3, 7]
def baseStart_4390862 : Nat := 118140960795 + 4390862 * 2 ^ 59
def prefixEnd_4390862 : Nat := 4983230072969 + 3 ^ 40 * 4390862 * 2
def baseEnd_4390862 : Nat := 250513632618011662881311

theorem tailTrace_4390862 : CollatzResearch.WordTrace tailWord_4390862 prefixEnd_4390862 250513632618011662881311 := by
  unfold tailWord_4390862
  simp only [CollatzResearch.WordTrace]
  refine ⟨20018486727333043546519855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106765262545776232248105893 20018486727333043546519855)
  ·
    refine ⟨30027730090999565319779783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20018486727333043546519855 30027730090999565319779783)
    ·
      refine ⟨45041595136499347979669675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30027730090999565319779783 45041595136499347979669675)
      ·
        refine ⟨67562392704749021969504513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45041595136499347979669675 67562392704749021969504513)
        ·
          refine ⟨50671794528561766477128385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67562392704749021969504513 50671794528561766477128385)
          ·
            refine ⟨38003845896421324857846289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50671794528561766477128385 38003845896421324857846289)
            ·
              refine ⟨28502884422315993643384717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38003845896421324857846289 28502884422315993643384717)
              ·
                refine ⟨10688581658368497616269269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28502884422315993643384717 10688581658368497616269269)
                ·
                  refine ⟨250513632618011662881311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10688581658368497616269269 250513632618011662881311)
                  ·
                    rfl

theorem cell23_4390862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 7].length) (baseStart_4390862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390862 prefixEnd_4390862 := by exact prefixLift 4390862
  have htrace : WordTrace (prefixWord ++ tailWord_4390862) baseStart_4390862 baseEnd_4390862 := by
    simpa [prefixWord, tailWord_4390862, baseEnd_4390862] using wordTrace_append hprefix tailTrace_4390862
  have hstable : (prefixWord ++ tailWord_4390862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390862).length < 2 ^ (prefixWord ++ tailWord_4390862).sum := by decide
  have hdescent : baseEnd_4390862 < baseStart_4390862 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390869 : List Nat := [1, 3, 2, 3, 2, 2, 1, 1, 2, 2, 4]
def baseStart_4390869 : Nat := 118140960795 + 4390869 * 2 ^ 59
def prefixEnd_4390869 : Nat := 4983230072969 + 3 ^ 40 * 4390869 * 2
def baseEnd_4390869 : Nat := 2254626287926686438544267

theorem tailTrace_4390869 : CollatzResearch.WordTrace tailWord_4390869 prefixEnd_4390869 2254626287926686438544267 := by
  unfold tailWord_4390869
  simp only [CollatzResearch.WordTrace]
  refine ⟨160148149129638988567663661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106765432753092659045109107 160148149129638988567663661)
  ·
    refine ⟨60055555923614620712873873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160148149129638988567663661 60055555923614620712873873)
    ·
      refine ⟨45041666942710965534655405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60055555923614620712873873 45041666942710965534655405)
      ·
        refine ⟨16890625103516612075495777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45041666942710965534655405 16890625103516612075495777)
        ·
          refine ⟨12667968827637459056621833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16890625103516612075495777 12667968827637459056621833)
          ·
            refine ⟨9500976620728094292466375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12667968827637459056621833 9500976620728094292466375)
            ·
              refine ⟨14251464931092141438699563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9500976620728094292466375 14251464931092141438699563)
              ·
                refine ⟨21377197396638212158049345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14251464931092141438699563 21377197396638212158049345)
                ·
                  refine ⟨16032898047478659118537009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21377197396638212158049345 16032898047478659118537009)
                  ·
                    refine ⟨12024673535608994338902757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16032898047478659118537009 12024673535608994338902757)
                    ·
                      refine ⟨2254626287926686438544267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12024673535608994338902757 2254626287926686438544267)
                      ·
                        rfl

theorem cell23_4390869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_4390869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390869 prefixEnd_4390869 := by exact prefixLift 4390869
  have htrace : WordTrace (prefixWord ++ tailWord_4390869) baseStart_4390869 baseEnd_4390869 := by
    simpa [prefixWord, tailWord_4390869, baseEnd_4390869] using wordTrace_append hprefix tailTrace_4390869
  have hstable : (prefixWord ++ tailWord_4390869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390869).length < 2 ^ (prefixWord ++ tailWord_4390869).sum := by decide
  have hdescent : baseEnd_4390869 < baseStart_4390869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390949 : List Nat := [1, 3, 1, 2, 2, 3, 2, 1, 1, 4, 3]
def baseStart_4390949 : Nat := 118140960795 + 4390949 * 2 ^ 59
def prefixEnd_4390949 : Nat := 4983230072969 + 3 ^ 40 * 4390949 * 2
def baseEnd_4390949 : Nat := 2254667366379046125543899

theorem tailTrace_4390949 : CollatzResearch.WordTrace tailWord_4390949 prefixEnd_4390949 2254667366379046125543899 := by
  unfold tailWord_4390949
  simp only [CollatzResearch.WordTrace]
  refine ⟨160151066969349162230575901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106767377979566108153717267 160151066969349162230575901)
  ·
    refine ⟨60056650113505935836465963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160151066969349162230575901 60056650113505935836465963)
    ·
      refine ⟨90084975170258903754698945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60056650113505935836465963 90084975170258903754698945)
      ·
        refine ⟨67563731377694177816024209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90084975170258903754698945 67563731377694177816024209)
        ·
          refine ⟨50672798533270633362018157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67563731377694177816024209 50672798533270633362018157)
          ·
            refine ⟨19002299449976487510756809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50672798533270633362018157 19002299449976487510756809)
            ·
              refine ⟨14251724587482365633067607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19002299449976487510756809 14251724587482365633067607)
              ·
                refine ⟨21377586881223548449601411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14251724587482365633067607 21377586881223548449601411)
                ·
                  refine ⟨32066380321835322674402117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21377586881223548449601411 32066380321835322674402117)
                  ·
                    refine ⟨6012446310344123001450397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32066380321835322674402117 6012446310344123001450397)
                    ·
                      refine ⟨2254667366379046125543899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6012446310344123001450397 2254667366379046125543899)
                      ·
                        rfl

theorem cell23_4390949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 4, 3].length) (baseStart_4390949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390949 prefixEnd_4390949 := by exact prefixLift 4390949
  have htrace : WordTrace (prefixWord ++ tailWord_4390949) baseStart_4390949 baseEnd_4390949 := by
    simpa [prefixWord, tailWord_4390949, baseEnd_4390949] using wordTrace_append hprefix tailTrace_4390949
  have hstable : (prefixWord ++ tailWord_4390949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390949).length < 2 ^ (prefixWord ++ tailWord_4390949).sum := by decide
  have hdescent : baseEnd_4390949 < baseStart_4390949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390956 : List Nat := [2, 2, 1, 1, 1, 2, 2, 7, 1, 4]
def baseStart_4390956 : Nat := 118140960795 + 4390956 * 2 ^ 59
def prefixEnd_4390956 : Nat := 4983230072969 + 3 ^ 40 * 4390956 * 2
def baseEnd_4390956 : Nat := 751556986914542532718789

theorem tailTrace_4390956 : CollatzResearch.WordTrace tailWord_4390956 prefixEnd_4390956 751556986914542532718789 := by
  unfold tailWord_4390956
  simp only [CollatzResearch.WordTrace]
  refine ⟨80075661140161901213040361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106767548186882534950720481 80075661140161901213040361)
  ·
    refine ⟨60056745855121425909780271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80075661140161901213040361 60056745855121425909780271)
    ·
      refine ⟨90085118782682138864670407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60056745855121425909780271 90085118782682138864670407)
      ·
        refine ⟨135127678174023208297005611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90085118782682138864670407 135127678174023208297005611)
        ·
          refine ⟨202691517261034812445508417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135127678174023208297005611 202691517261034812445508417)
          ·
            refine ⟨152018637945776109334131313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202691517261034812445508417 152018637945776109334131313)
            ·
              refine ⟨114013978459332082000598485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152018637945776109334131313 114013978459332082000598485)
              ·
                refine ⟨2672202620140595671889027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 114013978459332082000598485 2672202620140595671889027)
                ·
                  refine ⟨4008303930210893507833541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2672202620140595671889027 4008303930210893507833541)
                  ·
                    refine ⟨751556986914542532718789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4008303930210893507833541 751556986914542532718789)
                    ·
                      rfl

theorem cell23_4390956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 7, 1, 4].length) (baseStart_4390956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390956 prefixEnd_4390956 := by exact prefixLift 4390956
  have htrace : WordTrace (prefixWord ++ tailWord_4390956) baseStart_4390956 baseEnd_4390956 := by
    simpa [prefixWord, tailWord_4390956, baseEnd_4390956] using wordTrace_append hprefix tailTrace_4390956
  have hstable : (prefixWord ++ tailWord_4390956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390956).length < 2 ^ (prefixWord ++ tailWord_4390956).sum := by decide
  have hdescent : baseEnd_4390956 < baseStart_4390956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4390996 : List Nat := [2, 4, 1, 1, 1, 1, 1, 3, 5, 1, 3]
def baseStart_4390996 : Nat := 118140960795 + 4390996 * 2 ^ 59
def prefixEnd_4390996 : Nat := 4983230072969 + 3 ^ 40 * 4390996 * 2
def baseEnd_4390996 : Nat := 2254691499969807441656183

theorem tailTrace_4390996 : CollatzResearch.WordTrace tailWord_4390996 prefixEnd_4390996 2254691499969807441656183 := by
  unfold tailWord_4390996
  simp only [CollatzResearch.WordTrace]
  refine ⟨80076390600089444628768421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106768520800119259505024561 80076390600089444628768421)
  ·
    refine ⟨15014323237516770867894079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80076390600089444628768421 15014323237516770867894079)
    ·
      refine ⟨22521484856275156301841119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15014323237516770867894079 22521484856275156301841119)
      ·
        refine ⟨33782227284412734452761679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22521484856275156301841119 33782227284412734452761679)
        ·
          refine ⟨50673340926619101679142519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33782227284412734452761679 50673340926619101679142519)
          ·
            refine ⟨76010011389928652518713779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50673340926619101679142519 76010011389928652518713779)
            ·
              refine ⟨114015017084892978778070669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76010011389928652518713779 114015017084892978778070669)
              ·
                refine ⟨42755631406834867041776501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114015017084892978778070669 42755631406834867041776501)
                ·
                  refine ⟨4008340444390768785166547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42755631406834867041776501 4008340444390768785166547)
                  ·
                    refine ⟨6012510666586153177749821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4008340444390768785166547 6012510666586153177749821)
                    ·
                      refine ⟨2254691499969807441656183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6012510666586153177749821 2254691499969807441656183)
                      ·
                        rfl

theorem cell23_4390996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_4390996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4390996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4390996 prefixEnd_4390996 := by exact prefixLift 4390996
  have htrace : WordTrace (prefixWord ++ tailWord_4390996) baseStart_4390996 baseEnd_4390996 := by
    simpa [prefixWord, tailWord_4390996, baseEnd_4390996] using wordTrace_append hprefix tailTrace_4390996
  have hstable : (prefixWord ++ tailWord_4390996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4390996).length < 2 ^ (prefixWord ++ tailWord_4390996).sum := by decide
  have hdescent : baseEnd_4390996 < baseStart_4390996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4390996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391056 : List Nat := [2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 3]
def baseStart_4391056 : Nat := 118140960795 + 4391056 * 2 ^ 59
def prefixEnd_4391056 : Nat := 4983230072969 + 3 ^ 40 * 4391056 * 2
def baseEnd_4391056 : Nat := 2254722308809077206905907

theorem tailTrace_4391056 : CollatzResearch.WordTrace tailWord_4391056 prefixEnd_4391056 2254722308809077206905907 := by
  unfold tailWord_4391056
  simp only [CollatzResearch.WordTrace]
  refine ⟨80077484789980759752360511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106769979719974346336480681 80077484789980759752360511)
  ·
    refine ⟨120116227184971139628540767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80077484789980759752360511 120116227184971139628540767)
    ·
      refine ⟨180174340777456709442811151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120116227184971139628540767 180174340777456709442811151)
      ·
        refine ⟨270261511166185064164216727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180174340777456709442811151 270261511166185064164216727)
        ·
          refine ⟨405392266749277596246325091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270261511166185064164216727 405392266749277596246325091)
          ·
            refine ⟨608088400123916394369487637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405392266749277596246325091 608088400123916394369487637)
            ·
              refine ⟨28504143755808580986069733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 608088400123916394369487637 28504143755808580986069733)
              ·
                refine ⟨5344526954214108934888075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28504143755808580986069733 5344526954214108934888075)
                ·
                  refine ⟨8016790431321163402332113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5344526954214108934888075 8016790431321163402332113)
                  ·
                    refine ⟨6012592823490872551749085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8016790431321163402332113 6012592823490872551749085)
                    ·
                      refine ⟨2254722308809077206905907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6012592823490872551749085 2254722308809077206905907)
                      ·
                        rfl

theorem cell23_4391056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 3].length) (baseStart_4391056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391056 prefixEnd_4391056 := by exact prefixLift 4391056
  have htrace : WordTrace (prefixWord ++ tailWord_4391056) baseStart_4391056 baseEnd_4391056 := by
    simpa [prefixWord, tailWord_4391056, baseEnd_4391056] using wordTrace_append hprefix tailTrace_4391056
  have hstable : (prefixWord ++ tailWord_4391056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391056).length < 2 ^ (prefixWord ++ tailWord_4391056).sum := by decide
  have hdescent : baseEnd_4391056 < baseStart_4391056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391070 : List Nat := [4, 3, 1, 1, 3, 1, 1, 3, 1, 1, 4]
def baseStart_4391070 : Nat := 118140960795 + 4391070 * 2 ^ 59
def prefixEnd_4391070 : Nat := 4983230072969 + 3 ^ 40 * 4391070 * 2
def baseEnd_4391070 : Nat := 2254729497538240152130843

theorem tailTrace_4391070 : CollatzResearch.WordTrace tailWord_4391070 prefixEnd_4391070 2254729497538240152130843 := by
  unfold tailWord_4391070
  simp only [CollatzResearch.WordTrace]
  refine ⟨20019435025238849986966333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106770320134607199930487109 20019435025238849986966333)
  ·
    refine ⟨7507288134464568745112375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20019435025238849986966333 7507288134464568745112375)
    ·
      refine ⟨11260932201696853117668563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7507288134464568745112375 11260932201696853117668563)
      ·
        refine ⟨16891398302545279676502845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11260932201696853117668563 16891398302545279676502845)
        ·
          refine ⟨6334274363454479878688567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16891398302545279676502845 6334274363454479878688567)
          ·
            refine ⟨9501411545181719818032851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6334274363454479878688567 9501411545181719818032851)
            ·
              refine ⟨14252117317772579727049277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9501411545181719818032851 14252117317772579727049277)
              ·
                refine ⟨5344543994164717397643479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14252117317772579727049277 5344543994164717397643479)
                ·
                  refine ⟨8016815991247076096465219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5344543994164717397643479 8016815991247076096465219)
                  ·
                    refine ⟨12025223986870614144697829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8016815991247076096465219 12025223986870614144697829)
                    ·
                      refine ⟨2254729497538240152130843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12025223986870614144697829 2254729497538240152130843)
                      ·
                        rfl

theorem cell23_4391070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_4391070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391070 prefixEnd_4391070 := by exact prefixLift 4391070
  have htrace : WordTrace (prefixWord ++ tailWord_4391070) baseStart_4391070 baseEnd_4391070 := by
    simpa [prefixWord, tailWord_4391070, baseEnd_4391070] using wordTrace_append hprefix tailTrace_4391070
  have hstable : (prefixWord ++ tailWord_4391070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391070).length < 2 ^ (prefixWord ++ tailWord_4391070).sum := by decide
  have hdescent : baseEnd_4391070 < baseStart_4391070 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391073 : List Nat := [1, 2, 3, 3, 1, 3, 1, 3, 1, 2, 3]
def baseStart_4391073 : Nat := 118140960795 + 4391073 * 2 ^ 59
def prefixEnd_4391073 : Nat := 4983230072969 + 3 ^ 40 * 4391073 * 2
def baseEnd_4391073 : Nat := 2254731037980203640393329

theorem tailTrace_4391073 : CollatzResearch.WordTrace tailWord_4391073 prefixEnd_4391073 2254731037980203640393329 := by
  unfold tailWord_4391073
  simp only [CollatzResearch.WordTrace]
  refine ⟨160155589620899931408089873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106770393080599954272059915 160155589620899931408089873)
  ·
    refine ⟨120116692215674948556067405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160155589620899931408089873 120116692215674948556067405)
    ·
      refine ⟨45043759580878105708525277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120116692215674948556067405 45043759580878105708525277)
      ·
        refine ⟨16891409842829289640696979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45043759580878105708525277 16891409842829289640696979)
        ·
          refine ⟨25337114764243934461045469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16891409842829289640696979 25337114764243934461045469)
          ·
            refine ⟨9501418036591475422892051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25337114764243934461045469 9501418036591475422892051)
            ·
              refine ⟨14252127054887213134338077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9501418036591475422892051 14252127054887213134338077)
              ·
                refine ⟨5344547645582704925376779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14252127054887213134338077 5344547645582704925376779)
                ·
                  refine ⟨8016821468374057388065169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5344547645582704925376779 8016821468374057388065169)
                  ·
                    refine ⟨6012616101280543041048877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8016821468374057388065169 6012616101280543041048877)
                    ·
                      refine ⟨2254731037980203640393329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6012616101280543041048877 2254731037980203640393329)
                      ·
                        rfl

theorem cell23_4391073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_4391073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391073 prefixEnd_4391073 := by exact prefixLift 4391073
  have htrace : WordTrace (prefixWord ++ tailWord_4391073) baseStart_4391073 baseEnd_4391073 := by
    simpa [prefixWord, tailWord_4391073, baseEnd_4391073] using wordTrace_append hprefix tailTrace_4391073
  have hstable : (prefixWord ++ tailWord_4391073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391073).length < 2 ^ (prefixWord ++ tailWord_4391073).sum := by decide
  have hdescent : baseEnd_4391073 < baseStart_4391073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391100 : List Nat := [2, 2, 2, 3, 4, 1, 1, 1, 1, 2, 4]
def baseStart_4391100 : Nat := 118140960795 + 4391100 * 2 ^ 59
def prefixEnd_4391100 : Nat := 4983230072969 + 3 ^ 40 * 4391100 * 2
def baseEnd_4391100 : Nat := 2254744901957875034755705

theorem tailTrace_4391100 : CollatzResearch.WordTrace tailWord_4391100 prefixEnd_4391100 2254744901957875034755705 := by
  unfold tailWord_4391100
  simp only [CollatzResearch.WordTrace]
  refine ⟨80078287195901057509661377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106771049594534743346215169 80078287195901057509661377)
  ·
    refine ⟨60058715396925793132246033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80078287195901057509661377 60058715396925793132246033)
    ·
      refine ⟨45044036547694344849184525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60058715396925793132246033 45044036547694344849184525)
      ·
        refine ⟨16891513705385379318444197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45044036547694344849184525 16891513705385379318444197)
        ·
          refine ⟨3167158819759758622208287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16891513705385379318444197 3167158819759758622208287)
          ·
            refine ⟨4750738229639637933312431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3167158819759758622208287 4750738229639637933312431)
            ·
              refine ⟨7126107344459456899968647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4750738229639637933312431 7126107344459456899968647)
              ·
                refine ⟨10689161016689185349952971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7126107344459456899968647 10689161016689185349952971)
                ·
                  refine ⟨16033741525033778024929457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10689161016689185349952971 16033741525033778024929457)
                  ·
                    refine ⟨12025306143775333518697093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16033741525033778024929457 12025306143775333518697093)
                    ·
                      refine ⟨2254744901957875034755705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12025306143775333518697093 2254744901957875034755705)
                      ·
                        rfl

theorem cell23_4391100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_4391100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391100 prefixEnd_4391100 := by exact prefixLift 4391100
  have htrace : WordTrace (prefixWord ++ tailWord_4391100) baseStart_4391100 baseEnd_4391100 := by
    simpa [prefixWord, tailWord_4391100, baseEnd_4391100] using wordTrace_append hprefix tailTrace_4391100
  have hstable : (prefixWord ++ tailWord_4391100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391100).length < 2 ^ (prefixWord ++ tailWord_4391100).sum := by decide
  have hdescent : baseEnd_4391100 < baseStart_4391100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391109 : List Nat := [1, 3, 1, 1, 1, 1, 4, 2, 2, 3, 4]
def baseStart_4391109 : Nat := 118140960795 + 4391109 * 2 ^ 59
def prefixEnd_4391109 : Nat := 4983230072969 + 3 ^ 40 * 4391109 * 2
def baseEnd_4391109 : Nat := 2254749523283765499543163

theorem tailTrace_4391109 : CollatzResearch.WordTrace tailWord_4391109 prefixEnd_4391109 2254749523283765499543163 := by
  unfold tailWord_4391109
  simp only [CollatzResearch.WordTrace]
  refine ⟨160156902648769509556400381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106771268432513006370933587 160156902648769509556400381)
  ·
    refine ⟨60058838493288566083650143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160156902648769509556400381 60058838493288566083650143)
    ·
      refine ⟨90088257739932849125475215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60058838493288566083650143 90088257739932849125475215)
      ·
        refine ⟨135132386609899273688212823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90088257739932849125475215 135132386609899273688212823)
        ·
          refine ⟨202698579914848910532319235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135132386609899273688212823 202698579914848910532319235)
          ·
            refine ⟨304047869872273365798478853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202698579914848910532319235 304047869872273365798478853)
            ·
              refine ⟨57008975601051256087214785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 304047869872273365798478853 57008975601051256087214785)
              ·
                refine ⟨42756731700788442065411089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57008975601051256087214785 42756731700788442065411089)
                ·
                  refine ⟨32067548775591331549058317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42756731700788442065411089 32067548775591331549058317)
                  ·
                    refine ⟨12025330790846749330896869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32067548775591331549058317 12025330790846749330896869)
                    ·
                      refine ⟨2254749523283765499543163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12025330790846749330896869 2254749523283765499543163)
                      ·
                        rfl

theorem cell23_4391109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 3, 4].length) (baseStart_4391109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391109 prefixEnd_4391109 := by exact prefixLift 4391109
  have htrace : WordTrace (prefixWord ++ tailWord_4391109) baseStart_4391109 baseEnd_4391109 := by
    simpa [prefixWord, tailWord_4391109, baseEnd_4391109] using wordTrace_append hprefix tailTrace_4391109
  have hstable : (prefixWord ++ tailWord_4391109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391109).length < 2 ^ (prefixWord ++ tailWord_4391109).sum := by decide
  have hdescent : baseEnd_4391109 < baseStart_4391109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391129 : List Nat := [1, 2, 1, 2, 3, 1, 3, 1, 1, 3, 5]
def baseStart_4391129 : Nat := 118140960795 + 4391129 * 2 ^ 59
def prefixEnd_4391129 : Nat := 4983230072969 + 3 ^ 40 * 4391129 * 2
def baseEnd_4391129 : Nat := 2254759792896855421293071

theorem tailTrace_4391129 : CollatzResearch.WordTrace tailWord_4391129 prefixEnd_4391129 2254759792896855421293071 := by
  unfold tailWord_4391129
  simp only [CollatzResearch.WordTrace]
  refine ⟨160157632108697052972128441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106771754739131368648085627 160157632108697052972128441)
  ·
    refine ⟨120118224081522789729096331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160157632108697052972128441 120118224081522789729096331)
    ·
      refine ⟨180177336122284184593644497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120118224081522789729096331 180177336122284184593644497)
      ·
        refine ⟨135133002091713138445233373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180177336122284184593644497 135133002091713138445233373)
        ·
          refine ⟨50674875784392426916962515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135133002091713138445233373 50674875784392426916962515)
          ·
            refine ⟨76012313676588640375443773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50674875784392426916962515 76012313676588640375443773)
            ·
              refine ⟨28504617628720740140791415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76012313676588640375443773 28504617628720740140791415)
              ·
                refine ⟨42756926443081110211187123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28504617628720740140791415 42756926443081110211187123)
                ·
                  refine ⟨64135389664621665316780685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42756926443081110211187123 64135389664621665316780685)
                  ·
                    refine ⟨24050771124233124493792757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64135389664621665316780685 24050771124233124493792757)
                    ·
                      refine ⟨2254759792896855421293071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24050771124233124493792757 2254759792896855421293071)
                      ·
                        rfl

theorem cell23_4391129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_4391129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391129 prefixEnd_4391129 := by exact prefixLift 4391129
  have htrace : WordTrace (prefixWord ++ tailWord_4391129) baseStart_4391129 baseEnd_4391129 := by
    simpa [prefixWord, tailWord_4391129, baseEnd_4391129] using wordTrace_append hprefix tailTrace_4391129
  have hstable : (prefixWord ++ tailWord_4391129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391129).length < 2 ^ (prefixWord ++ tailWord_4391129).sum := by decide
  have hdescent : baseEnd_4391129 < baseStart_4391129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391138 : List Nat := [3, 3, 4, 1, 2, 1, 1, 1, 3, 2, 2]
def baseStart_4391138 : Nat := 118140960795 + 4391138 * 2 ^ 59
def prefixEnd_4391138 : Nat := 4983230072969 + 3 ^ 40 * 4391138 * 2
def baseEnd_4391138 : Nat := 2254764414222745886080531

theorem tailTrace_4391138 : CollatzResearch.WordTrace tailWord_4391138 prefixEnd_4391138 2254764414222745886080531 := by
  unfold tailWord_4391138
  simp only [CollatzResearch.WordTrace]
  refine ⟨40039490091416111877301517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106771973577109631672804045 40039490091416111877301517)
  ·
    refine ⟨15014808784281041953988069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40039490091416111877301517 15014808784281041953988069)
    ·
      refine ⟨2815276647052695366372763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15014808784281041953988069 2815276647052695366372763)
      ·
        refine ⟨4222914970579043049559145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2815276647052695366372763 4222914970579043049559145)
        ·
          refine ⟨3167186227934282287169359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4222914970579043049559145 3167186227934282287169359)
          ·
            refine ⟨4750779341901423430754039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3167186227934282287169359 4750779341901423430754039)
            ·
              refine ⟨7126169012852135146131059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4750779341901423430754039 7126169012852135146131059)
              ·
                refine ⟨10689253519278202719196589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7126169012852135146131059 10689253519278202719196589)
                ·
                  refine ⟨4008470069729326019698721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10689253519278202719196589 4008470069729326019698721)
                  ·
                    refine ⟨3006352552296994514774041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4008470069729326019698721 3006352552296994514774041)
                    ·
                      refine ⟨2254764414222745886080531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3006352552296994514774041 2254764414222745886080531)
                      ·
                        rfl

theorem cell23_4391138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_4391138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391138 prefixEnd_4391138 := by exact prefixLift 4391138
  have htrace : WordTrace (prefixWord ++ tailWord_4391138) baseStart_4391138 baseEnd_4391138 := by
    simpa [prefixWord, tailWord_4391138, baseEnd_4391138] using wordTrace_append hprefix tailTrace_4391138
  have hstable : (prefixWord ++ tailWord_4391138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391138).length < 2 ^ (prefixWord ++ tailWord_4391138).sum := by decide
  have hdescent : baseEnd_4391138 < baseStart_4391138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391146 : List Nat := [3, 1, 3, 1, 1, 2, 2, 1, 2, 4, 3]
def baseStart_4391146 : Nat := 118140960795 + 4391146 * 2 ^ 59
def prefixEnd_4391146 : Nat := 4983230072969 + 3 ^ 40 * 4391146 * 2
def baseEnd_4391146 : Nat := 2254768522067981854780493

theorem tailTrace_4391146 : CollatzResearch.WordTrace tailWord_4391146 prefixEnd_4391146 2254768522067981854780493 := by
  unfold tailWord_4391146
  simp only [CollatzResearch.WordTrace]
  refine ⟨40039563037408866218874323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106772168099756976583664861 40039563037408866218874323)
  ·
    refine ⟨60059344556113299328311485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40039563037408866218874323 60059344556113299328311485)
    ·
      refine ⟨22522254208542487248116807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60059344556113299328311485 22522254208542487248116807)
      ·
        refine ⟨33783381312813730872175211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22522254208542487248116807 33783381312813730872175211)
        ·
          refine ⟨50675071969220596308262817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33783381312813730872175211 50675071969220596308262817)
          ·
            refine ⟨38006303976915447231197113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50675071969220596308262817 38006303976915447231197113)
            ·
              refine ⟨28504727982686585423397835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38006303976915447231197113 28504727982686585423397835)
              ·
                refine ⟨42757091974029878135096753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28504727982686585423397835 42757091974029878135096753)
                ·
                  refine ⟨32067818980522408601322565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42757091974029878135096753 32067818980522408601322565)
                  ·
                    refine ⟨6012716058847951612747981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32067818980522408601322565 6012716058847951612747981)
                    ·
                      refine ⟨2254768522067981854780493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6012716058847951612747981 2254768522067981854780493)
                      ·
                        rfl

theorem cell23_4391146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_4391146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391146 prefixEnd_4391146 := by exact prefixLift 4391146
  have htrace : WordTrace (prefixWord ++ tailWord_4391146) baseStart_4391146 baseEnd_4391146 := by
    simpa [prefixWord, tailWord_4391146, baseEnd_4391146] using wordTrace_append hprefix tailTrace_4391146
  have hstable : (prefixWord ++ tailWord_4391146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391146).length < 2 ^ (prefixWord ++ tailWord_4391146).sum := by decide
  have hdescent : baseEnd_4391146 < baseStart_4391146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391166 : List Nat := [4, 2, 2, 1, 1, 1, 2, 1, 9]
def baseStart_4391166 : Nat := 118140960795 + 4391166 * 2 ^ 59
def prefixEnd_4391166 : Nat := 4983230072969 + 3 ^ 40 * 4391166 * 2
def baseEnd_4391166 : Nat := 250530976853452419614489

theorem tailTrace_4391166 : CollatzResearch.WordTrace tailWord_4391166 prefixEnd_4391166 250530976853452419614489 := by
  unfold tailWord_4391166
  simp only [CollatzResearch.WordTrace]
  refine ⟨20019872701195376036403169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106772654406375338860816901 20019872701195376036403169)
  ·
    refine ⟨15014904525896532027302377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20019872701195376036403169 15014904525896532027302377)
    ·
      refine ⟨11261178394422399020476783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15014904525896532027302377 11261178394422399020476783)
      ·
        refine ⟨16891767591633598530715175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11261178394422399020476783 16891767591633598530715175)
        ·
          refine ⟨25337651387450397796072763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16891767591633598530715175 25337651387450397796072763)
          ·
            refine ⟨38006477081175596694109145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25337651387450397796072763 38006477081175596694109145)
            ·
              refine ⟨28504857810881697520581859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38006477081175596694109145 28504857810881697520581859)
              ·
                refine ⟨42757286716322546280872789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28504857810881697520581859 42757286716322546280872789)
                ·
                  refine ⟨250530976853452419614489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 42757286716322546280872789 250530976853452419614489)
                  ·
                    rfl

theorem cell23_4391166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_4391166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391166 prefixEnd_4391166 := by exact prefixLift 4391166
  have htrace : WordTrace (prefixWord ++ tailWord_4391166) baseStart_4391166 baseEnd_4391166 := by
    simpa [prefixWord, tailWord_4391166, baseEnd_4391166] using wordTrace_append hprefix tailTrace_4391166
  have hstable : (prefixWord ++ tailWord_4391166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391166).length < 2 ^ (prefixWord ++ tailWord_4391166).sum := by decide
  have hdescent : baseEnd_4391166 < baseStart_4391166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391200 : List Nat := [2, 1, 1, 5, 2, 1, 4, 2, 5]
def baseStart_4391200 : Nat := 118140960795 + 4391200 * 2 ^ 59
def prefixEnd_4391200 : Nat := 4983230072969 + 3 ^ 40 * 4391200 * 2
def baseEnd_4391200 : Nat := 250532916669258293722805

theorem tailTrace_4391200 : CollatzResearch.WordTrace tailWord_4391200 prefixEnd_4391200 250532916669258293722805 := by
  unfold tailWord_4391200
  simp only [CollatzResearch.WordTrace]
  refine ⟨80080110845719916048981527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106773481127626554731975369 80080110845719916048981527)
  ·
    refine ⟨120120166268579874073472291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80080110845719916048981527 120120166268579874073472291)
    ·
      refine ⟨180180249402869811110208437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120120166268579874073472291 180180249402869811110208437)
      ·
        refine ⟨16891898381519044791582041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 180180249402869811110208437 16891898381519044791582041)
        ·
          refine ⟨12668923786139283593686531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16891898381519044791582041 12668923786139283593686531)
          ·
            refine ⟨19003385679208925390529797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12668923786139283593686531 19003385679208925390529797)
            ·
              refine ⟨3563134814851673510724337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19003385679208925390529797 3563134814851673510724337)
              ·
                refine ⟨2672351111138755133043253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3563134814851673510724337 2672351111138755133043253)
                ·
                  refine ⟨250532916669258293722805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2672351111138755133043253 250532916669258293722805)
                  ·
                    rfl

theorem cell23_4391200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 2, 5].length) (baseStart_4391200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391200 prefixEnd_4391200 := by exact prefixLift 4391200
  have htrace : WordTrace (prefixWord ++ tailWord_4391200) baseStart_4391200 baseEnd_4391200 := by
    simpa [prefixWord, tailWord_4391200, baseEnd_4391200] using wordTrace_append hprefix tailTrace_4391200
  have hstable : (prefixWord ++ tailWord_4391200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391200).length < 2 ^ (prefixWord ++ tailWord_4391200).sum := by decide
  have hdescent : baseEnd_4391200 < baseStart_4391200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391207 : List Nat := [1, 1, 8, 1, 1, 1, 1, 1, 2, 2, 4]
def baseStart_4391207 : Nat := 118140960795 + 4391207 * 2 ^ 59
def prefixEnd_4391207 : Nat := 4983230072969 + 3 ^ 40 * 4391207 * 2
def baseEnd_4391207 : Nat := 2254799844387906116117713

theorem tailTrace_4391207 : CollatzResearch.WordTrace tailWord_4391207 prefixEnd_4391207 2254799844387906116117713 := by
  unfold tailWord_4391207
  simp only [CollatzResearch.WordTrace]
  refine ⟨160160477002414472293467875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106773651334942981528978583 160160477002414472293467875)
  ·
    refine ⟨240240715503621708440201813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160160477002414472293467875 240240715503621708440201813)
    ·
      refine ⟨2815320884808066895783615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 240240715503621708440201813 2815320884808066895783615)
      ·
        refine ⟨4222981327212100343675423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2815320884808066895783615 4222981327212100343675423)
        ·
          refine ⟨6334471990818150515513135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4222981327212100343675423 6334471990818150515513135)
          ·
            refine ⟨9501707986227225773269703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6334471990818150515513135 9501707986227225773269703)
            ·
              refine ⟨14252561979340838659904555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9501707986227225773269703 14252561979340838659904555)
              ·
                refine ⟨21378842969011257989856833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14252561979340838659904555 21378842969011257989856833)
                ·
                  refine ⟨16034132226758443492392625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21378842969011257989856833 16034132226758443492392625)
                  ·
                    refine ⟨12025599170068832619294469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16034132226758443492392625 12025599170068832619294469)
                    ·
                      refine ⟨2254799844387906116117713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12025599170068832619294469 2254799844387906116117713)
                      ·
                        rfl

theorem cell23_4391207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_4391207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391207 prefixEnd_4391207 := by exact prefixLift 4391207
  have htrace : WordTrace (prefixWord ++ tailWord_4391207) baseStart_4391207 baseEnd_4391207 := by
    simpa [prefixWord, tailWord_4391207, baseEnd_4391207] using wordTrace_append hprefix tailTrace_4391207
  have hstable : (prefixWord ++ tailWord_4391207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391207).length < 2 ^ (prefixWord ++ tailWord_4391207).sum := by decide
  have hdescent : baseEnd_4391207 < baseStart_4391207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391210 : List Nat := [3, 1, 4, 2, 2, 1, 1, 1, 2, 3, 3]
def baseStart_4391210 : Nat := 118140960795 + 4391210 * 2 ^ 59
def prefixEnd_4391210 : Nat := 4983230072969 + 3 ^ 40 * 4391210 * 2
def baseEnd_4391210 : Nat := 2254801384829869604380199

theorem tailTrace_4391210 : CollatzResearch.WordTrace tailWord_4391210 prefixEnd_4391210 2254801384829869604380199 := by
  unfold tailWord_4391210
  simp only [CollatzResearch.WordTrace]
  refine ⟨40040146605350900951456771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106773724280935735870551389 40040146605350900951456771)
  ·
    refine ⟨60060219908026351427185157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40040146605350900951456771 60060219908026351427185157)
    ·
      refine ⟨11261291232754940892597217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60060219908026351427185157 11261291232754940892597217)
      ·
        refine ⟨8445968424566205669447913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11261291232754940892597217 8445968424566205669447913)
        ·
          refine ⟨6334476318424654252085935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8445968424566205669447913 6334476318424654252085935)
          ·
            refine ⟨9501714477636981378128903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6334476318424654252085935 9501714477636981378128903)
            ·
              refine ⟨14252571716455472067193355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9501714477636981378128903 14252571716455472067193355)
              ·
                refine ⟨21378857574683208100790033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14252571716455472067193355 21378857574683208100790033)
                ·
                  refine ⟨16034143181012406075592525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21378857574683208100790033 16034143181012406075592525)
                  ·
                    refine ⟨6012803692879652278347197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16034143181012406075592525 6012803692879652278347197)
                    ·
                      refine ⟨2254801384829869604380199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6012803692879652278347197 2254801384829869604380199)
                      ·
                        rfl

theorem cell23_4391210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_4391210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391210 prefixEnd_4391210 := by exact prefixLift 4391210
  have htrace : WordTrace (prefixWord ++ tailWord_4391210) baseStart_4391210 baseEnd_4391210 := by
    simpa [prefixWord, tailWord_4391210, baseEnd_4391210] using wordTrace_append hprefix tailTrace_4391210
  have hstable : (prefixWord ++ tailWord_4391210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391210).length < 2 ^ (prefixWord ++ tailWord_4391210).sum := by decide
  have hdescent : baseEnd_4391210 < baseStart_4391210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391230 : List Nat := [4, 2, 1, 2, 1, 4, 1, 1, 2, 5]
def baseStart_4391230 : Nat := 118140960795 + 4391230 * 2 ^ 59
def prefixEnd_4391230 : Nat := 4983230072969 + 3 ^ 40 * 4391230 * 2
def baseEnd_4391230 : Nat := 751603884814319842043369

theorem tailTrace_4391230 : CollatzResearch.WordTrace tailWord_4391230 prefixEnd_4391230 751603884814319842043369 := by
  unfold tailWord_4391230
  simp only [CollatzResearch.WordTrace]
  refine ⟨20020164485166393402694393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106774210587554098147703429 20020164485166393402694393)
  ·
    refine ⟨15015123363874795052020795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20020164485166393402694393 15015123363874795052020795)
    ·
      refine ⟨22522685045812192578031193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15015123363874795052020795 22522685045812192578031193)
      ·
        refine ⟨16892013784359144433523395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22522685045812192578031193 16892013784359144433523395)
        ·
          refine ⟨25338020676538716650285093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16892013784359144433523395 25338020676538716650285093)
          ·
            refine ⟨4750878876851009371928455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25338020676538716650285093 4750878876851009371928455)
            ·
              refine ⟨7126318315276514057892683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4750878876851009371928455 7126318315276514057892683)
              ·
                refine ⟨10689477472914771086839025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7126318315276514057892683 10689477472914771086839025)
                ·
                  refine ⟨8017108104686078315129269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10689477472914771086839025 8017108104686078315129269)
                  ·
                    refine ⟨751603884814319842043369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8017108104686078315129269 751603884814319842043369)
                    ·
                      rfl

theorem cell23_4391230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_4391230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391230 prefixEnd_4391230 := by exact prefixLift 4391230
  have htrace : WordTrace (prefixWord ++ tailWord_4391230) baseStart_4391230 baseEnd_4391230 := by
    simpa [prefixWord, tailWord_4391230, baseEnd_4391230] using wordTrace_append hprefix tailTrace_4391230
  have hstable : (prefixWord ++ tailWord_4391230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391230).length < 2 ^ (prefixWord ++ tailWord_4391230).sum := by decide
  have hdescent : baseEnd_4391230 < baseStart_4391230 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391256 : List Nat := [2, 1, 2, 2, 1, 1, 2, 6, 6]
def baseStart_4391256 : Nat := 118140960795 + 4391256 * 2 ^ 59
def prefixEnd_4391256 : Nat := 4983230072969 + 3 ^ 40 * 4391256 * 2
def baseEnd_4391256 : Nat := 250536111659997380489443

theorem tailTrace_4391256 : CollatzResearch.WordTrace tailWord_4391256 prefixEnd_4391256 250536111659997380489443 := by
  unfold tailWord_4391256
  simp only [CollatzResearch.WordTrace]
  refine ⟨80081132089618476831000811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106774842786157969108001081 80081132089618476831000811)
  ·
    refine ⟨120121698134427715246501217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80081132089618476831000811 120121698134427715246501217)
    ·
      refine ⟨90091273600820786434875913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120121698134427715246501217 90091273600820786434875913)
      ·
        refine ⟨67568455200615589826156935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90091273600820786434875913 67568455200615589826156935)
        ·
          refine ⟨101352682800923384739235403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67568455200615589826156935 101352682800923384739235403)
          ·
            refine ⟨152029024201385077108853105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101352682800923384739235403 152029024201385077108853105)
            ·
              refine ⟨114021768151038807831639829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152029024201385077108853105 114021768151038807831639829)
              ·
                refine ⟨5344770382079944117108117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 114021768151038807831639829 5344770382079944117108117)
                ·
                  refine ⟨250536111659997380489443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5344770382079944117108117 250536111659997380489443)
                  ·
                    rfl

theorem cell23_4391256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 6].length) (baseStart_4391256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391256 prefixEnd_4391256 := by exact prefixLift 4391256
  have htrace : WordTrace (prefixWord ++ tailWord_4391256) baseStart_4391256 baseEnd_4391256 := by
    simpa [prefixWord, tailWord_4391256, baseEnd_4391256] using wordTrace_append hprefix tailTrace_4391256
  have hstable : (prefixWord ++ tailWord_4391256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391256).length < 2 ^ (prefixWord ++ tailWord_4391256).sum := by decide
  have hdescent : baseEnd_4391256 < baseStart_4391256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391273 : List Nat := [1, 2, 1, 1, 1, 3, 7, 1, 6]
def baseStart_4391273 : Nat := 118140960795 + 4391273 * 2 ^ 59
def prefixEnd_4391273 : Nat := 4983230072969 + 3 ^ 40 * 4391273 * 2
def baseEnd_4391273 : Nat := 250537081567900317543601

theorem tailTrace_4391273 : CollatzResearch.WordTrace tailWord_4391273 prefixEnd_4391273 250537081567900317543601 := by
  unfold tailWord_4391273
  simp only [CollatzResearch.WordTrace]
  refine ⟨160162884220175365565370473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106775256146783577043580315 160162884220175365565370473)
  ·
    refine ⟨120122163165131524174027855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160162884220175365565370473 120122163165131524174027855)
    ·
      refine ⟨180183244747697286261041783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120122163165131524174027855 180183244747697286261041783)
      ·
        refine ⟨270274867121545929391562675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180183244747697286261041783 270274867121545929391562675)
        ·
          refine ⟨405412300682318894087344013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270274867121545929391562675 405412300682318894087344013)
          ·
            refine ⟨152029612755869585282754005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 405412300682318894087344013 152029612755869585282754005)
            ·
              refine ⟨3563194048965693405064547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 152029612755869585282754005 3563194048965693405064547)
              ·
                refine ⟨5344791073448540107596821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3563194048965693405064547 5344791073448540107596821)
                ·
                  refine ⟨250537081567900317543601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5344791073448540107596821 250537081567900317543601)
                  ·
                    rfl

theorem cell23_4391273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 6].length) (baseStart_4391273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391273 prefixEnd_4391273 := by exact prefixLift 4391273
  have htrace : WordTrace (prefixWord ++ tailWord_4391273) baseStart_4391273 baseEnd_4391273 := by
    simpa [prefixWord, tailWord_4391273, baseEnd_4391273] using wordTrace_append hprefix tailTrace_4391273
  have hstable : (prefixWord ++ tailWord_4391273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391273).length < 2 ^ (prefixWord ++ tailWord_4391273).sum := by decide
  have hdescent : baseEnd_4391273 < baseStart_4391273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391303 : List Nat := [1, 1, 4, 2, 2, 1, 1, 5, 1, 5]
def baseStart_4391303 : Nat := 118140960795 + 4391303 * 2 ^ 59
def prefixEnd_4391303 : Nat := 4983230072969 + 3 ^ 40 * 4391303 * 2
def baseEnd_4391303 : Nat := 751616379510245913505757

theorem tailTrace_4391303 : CollatzResearch.WordTrace tailWord_4391303 prefixEnd_4391303 751616379510245913505757 := by
  unfold tailWord_4391303
  simp only [CollatzResearch.WordTrace]
  refine ⟨160163978410066680688962563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106775985606711120459308375 160163978410066680688962563)
  ·
    refine ⟨240245967615100021033443845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160163978410066680688962563 240245967615100021033443845)
    ·
      refine ⟨45046118927831253943770721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 240245967615100021033443845 45046118927831253943770721)
      ·
        refine ⟨33784589195873440457828041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45046118927831253943770721 33784589195873440457828041)
        ·
          refine ⟨25338441896905080343371031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33784589195873440457828041 25338441896905080343371031)
          ·
            refine ⟨38007662845357620515056547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25338441896905080343371031 38007662845357620515056547)
            ·
              refine ⟨57011494268036430772584821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38007662845357620515056547 57011494268036430772584821)
              ·
                refine ⟨5344827587628415384929827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57011494268036430772584821 5344827587628415384929827)
                ·
                  refine ⟨8017241381442623077394741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5344827587628415384929827 8017241381442623077394741)
                  ·
                    refine ⟨751616379510245913505757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8017241381442623077394741 751616379510245913505757)
                    ·
                      rfl

theorem cell23_4391303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_4391303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391303 prefixEnd_4391303 := by exact prefixLift 4391303
  have htrace : WordTrace (prefixWord ++ tailWord_4391303) baseStart_4391303 baseEnd_4391303 := by
    simpa [prefixWord, tailWord_4391303, baseEnd_4391303] using wordTrace_append hprefix tailTrace_4391303
  have hstable : (prefixWord ++ tailWord_4391303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391303).length < 2 ^ (prefixWord ++ tailWord_4391303).sum := by decide
  have hdescent : baseEnd_4391303 < baseStart_4391303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391340 : List Nat := [2, 2, 1, 1, 1, 1, 3, 3, 5, 2, 2]
def baseStart_4391340 : Nat := 118140960795 + 4391340 * 2 ^ 59
def prefixEnd_4391340 : Nat := 4983230072969 + 3 ^ 40 * 4391340 * 2
def baseEnd_4391340 : Nat := 2254868137314954095754601

theorem tailTrace_4391340 : CollatzResearch.WordTrace tailWord_4391340 prefixEnd_4391340 2254868137314954095754601 := by
  unfold tailWord_4391340
  simp only [CollatzResearch.WordTrace]
  refine ⟨80082663955466318004029737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106776885273955090672039649 80082663955466318004029737)
  ·
    refine ⟨60061997966599738503022303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80082663955466318004029737 60061997966599738503022303)
    ·
      refine ⟨90092996949899607754533455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60061997966599738503022303 90092996949899607754533455)
      ·
        refine ⟨135139495424849411631800183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90092996949899607754533455 135139495424849411631800183)
        ·
          refine ⟨202709243137274117447700275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135139495424849411631800183 202709243137274117447700275)
          ·
            refine ⟨304063864705911176171550413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202709243137274117447700275 304063864705911176171550413)
            ·
              refine ⟨114023949264716691064331405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 304063864705911176171550413 114023949264716691064331405)
              ·
                refine ⟨42758980974268759149124277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114023949264716691064331405 42758980974268759149124277)
                ·
                  refine ⟨4008654466337696170230401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42758980974268759149124277 4008654466337696170230401)
                  ·
                    refine ⟨3006490849753272127672801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4008654466337696170230401 3006490849753272127672801)
                    ·
                      refine ⟨2254868137314954095754601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3006490849753272127672801 2254868137314954095754601)
                      ·
                        rfl

theorem cell23_4391340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 2, 2].length) (baseStart_4391340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391340 prefixEnd_4391340 := by exact prefixLift 4391340
  have htrace : WordTrace (prefixWord ++ tailWord_4391340) baseStart_4391340 baseEnd_4391340 := by
    simpa [prefixWord, tailWord_4391340, baseEnd_4391340] using wordTrace_append hprefix tailTrace_4391340
  have hstable : (prefixWord ++ tailWord_4391340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391340).length < 2 ^ (prefixWord ++ tailWord_4391340).sum := by decide
  have hdescent : baseEnd_4391340 < baseStart_4391340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391346 : List Nat := [3, 2, 1, 1, 1, 1, 3, 11]
def baseStart_4391346 : Nat := 118140960795 + 4391346 * 2 ^ 59
def prefixEnd_4391346 : Nat := 4983230072969 + 3 ^ 40 * 4391346 * 2
def baseEnd_4391346 : Nat := 83513748822180780454799

theorem tailTrace_4391346 : CollatzResearch.WordTrace tailWord_4391346 prefixEnd_4391346 83513748822180780454799 := by
  unfold tailWord_4391346
  simp only [CollatzResearch.WordTrace]
  refine ⟨40041386687227724758194473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106777031165940599355185261 40041386687227724758194473)
  ·
    refine ⟨30031040015420793568645855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40041386687227724758194473 30031040015420793568645855)
    ·
      refine ⟨45046560023131190352968783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30031040015420793568645855 45046560023131190352968783)
      ·
        refine ⟨67569840034696785529453175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45046560023131190352968783 67569840034696785529453175)
        ·
          refine ⟨101354760052045178294179763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67569840034696785529453175 101354760052045178294179763)
          ·
            refine ⟨152032140078067767441269645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101354760052045178294179763 152032140078067767441269645)
            ·
              refine ⟨57012052529275412790476117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 152032140078067767441269645 57012052529275412790476117)
              ·
                refine ⟨83513748822180780454799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 57012052529275412790476117 83513748822180780454799)
                ·
                  rfl

theorem cell23_4391346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 11].length) (baseStart_4391346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391346 prefixEnd_4391346 := by exact prefixLift 4391346
  have htrace : WordTrace (prefixWord ++ tailWord_4391346) baseStart_4391346 baseEnd_4391346 := by
    simpa [prefixWord, tailWord_4391346, baseEnd_4391346] using wordTrace_append hprefix tailTrace_4391346
  have hstable : (prefixWord ++ tailWord_4391346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391346).length < 2 ^ (prefixWord ++ tailWord_4391346).sum := by decide
  have hdescent : baseEnd_4391346 < baseStart_4391346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391353 : List Nat := [1, 2, 1, 4, 3, 1, 1, 1, 3, 2, 4]
def baseStart_4391353 : Nat := 118140960795 + 4391353 * 2 ^ 59
def prefixEnd_4391353 : Nat := 4983230072969 + 3 ^ 40 * 4391353 * 2
def baseEnd_4391353 : Nat := 2254874812563462544892041

theorem tailTrace_4391353 : CollatzResearch.WordTrace tailWord_4391353 prefixEnd_4391353 2254874812563462544892041 := by
  unfold tailWord_4391353
  simp only [CollatzResearch.WordTrace]
  refine ⟨160165802059885539228282713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106777201373257026152188475 160165802059885539228282713)
  ·
    refine ⟨120124351544914154421212035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160165802059885539228282713 120124351544914154421212035)
    ·
      refine ⟨180186527317371231631818053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120124351544914154421212035 180186527317371231631818053)
      ·
        refine ⟨33784973872007105930965885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 180186527317371231631818053 33784973872007105930965885)
        ·
          refine ⟨12669365202002664724112207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33784973872007105930965885 12669365202002664724112207)
          ·
            refine ⟨19004047803003997086168311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12669365202002664724112207 19004047803003997086168311)
            ·
              refine ⟨28506071704505995629252467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19004047803003997086168311 28506071704505995629252467)
              ·
                refine ⟨42759107556758993443878701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28506071704505995629252467 42759107556758993443878701)
                ·
                  refine ⟨16034665333784622541454513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42759107556758993443878701 16034665333784622541454513)
                  ·
                    refine ⟨12025999000338466906090885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16034665333784622541454513 12025999000338466906090885)
                    ·
                      refine ⟨2254874812563462544892041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12025999000338466906090885 2254874812563462544892041)
                      ·
                        rfl

theorem cell23_4391353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_4391353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391353 prefixEnd_4391353 := by exact prefixLift 4391353
  have htrace : WordTrace (prefixWord ++ tailWord_4391353) baseStart_4391353 baseEnd_4391353 := by
    simpa [prefixWord, tailWord_4391353, baseEnd_4391353] using wordTrace_append hprefix tailTrace_4391353
  have hstable : (prefixWord ++ tailWord_4391353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391353).length < 2 ^ (prefixWord ++ tailWord_4391353).sum := by decide
  have hdescent : baseEnd_4391353 < baseStart_4391353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391357 : List Nat := [1, 4, 1, 2, 2, 3, 3, 1, 1, 1, 4]
def baseStart_4391357 : Nat := 118140960795 + 4391357 * 2 ^ 59
def prefixEnd_4391357 : Nat := 4983230072969 + 3 ^ 40 * 4391357 * 2
def baseEnd_4391357 : Nat := 2254876866486080529242023

theorem tailTrace_4391357 : CollatzResearch.WordTrace tailWord_4391357 prefixEnd_4391357 2254876866486080529242023 := by
  unfold tailWord_4391357
  simp only [CollatzResearch.WordTrace]
  refine ⟨160165947951871047911428325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106777298634580698607618883 160165947951871047911428325)
  ·
    refine ⟨30031115240975821483392811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160165947951871047911428325 30031115240975821483392811)
    ·
      refine ⟨45046672861463732225089217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30031115240975821483392811 45046672861463732225089217)
      ·
        refine ⟨33785004646097799168816913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45046672861463732225089217 33785004646097799168816913)
        ·
          refine ⟨25338753484573349376612685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33785004646097799168816913 25338753484573349376612685)
          ·
            refine ⟨9502032556715006016229757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25338753484573349376612685 9502032556715006016229757)
            ·
              refine ⟨3563262208768127256086159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9502032556715006016229757 3563262208768127256086159)
              ·
                refine ⟨5344893313152190884129239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3563262208768127256086159 5344893313152190884129239)
                ·
                  refine ⟨8017339969728286326193859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5344893313152190884129239 8017339969728286326193859)
                  ·
                    refine ⟨12026009954592429489290789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8017339969728286326193859 12026009954592429489290789)
                    ·
                      refine ⟨2254876866486080529242023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12026009954592429489290789 2254876866486080529242023)
                      ·
                        rfl

theorem cell23_4391357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_4391357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391357 prefixEnd_4391357 := by exact prefixLift 4391357
  have htrace : WordTrace (prefixWord ++ tailWord_4391357) baseStart_4391357 baseEnd_4391357 := by
    simpa [prefixWord, tailWord_4391357, baseEnd_4391357] using wordTrace_append hprefix tailTrace_4391357
  have hstable : (prefixWord ++ tailWord_4391357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391357).length < 2 ^ (prefixWord ++ tailWord_4391357).sum := by decide
  have hdescent : baseEnd_4391357 < baseStart_4391357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391380 : List Nat := [2, 4, 1, 2, 2, 3, 1, 8]
def baseStart_4391380 : Nat := 118140960795 + 4391380 * 2 ^ 59
def prefixEnd_4391380 : Nat := 4983230072969 + 3 ^ 40 * 4391380 * 2
def baseEnd_4391380 : Nat := 83514395427449405157571

theorem tailTrace_4391380 : CollatzResearch.WordTrace tailWord_4391380 prefixEnd_4391380 83514395427449405157571 := by
  unfold tailWord_4391380
  simp only [CollatzResearch.WordTrace]
  refine ⟨80083393415393861419757797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106777857887191815226343729 80083393415393861419757797)
  ·
    refine ⟨15015636265386349016204587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80083393415393861419757797 15015636265386349016204587)
    ·
      refine ⟨22523454398079523524306881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15015636265386349016204587 22523454398079523524306881)
      ·
        refine ⟨16892590798559642643230161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22523454398079523524306881 16892590798559642643230161)
        ·
          refine ⟨12669443098919731982422621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16892590798559642643230161 12669443098919731982422621)
          ·
            refine ⟨4751041162094899493408483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12669443098919731982422621 4751041162094899493408483)
            ·
              refine ⟨7126561743142349240112725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4751041162094899493408483 7126561743142349240112725)
              ·
                refine ⟨83514395427449405157571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7126561743142349240112725 83514395427449405157571)
                ·
                  rfl

theorem cell23_4391380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 8].length) (baseStart_4391380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391380 prefixEnd_4391380 := by exact prefixLift 4391380
  have htrace : WordTrace (prefixWord ++ tailWord_4391380) baseStart_4391380 baseEnd_4391380 := by
    simpa [prefixWord, tailWord_4391380, baseEnd_4391380] using wordTrace_append hprefix tailTrace_4391380
  have hstable : (prefixWord ++ tailWord_4391380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391380).length < 2 ^ (prefixWord ++ tailWord_4391380).sum := by decide
  have hdescent : baseEnd_4391380 < baseStart_4391380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391433 : List Nat := [1, 2, 1, 1, 3, 1, 2, 3, 2, 4, 3]
def baseStart_4391433 : Nat := 118140960795 + 4391433 * 2 ^ 59
def prefixEnd_4391433 : Nat := 4983230072969 + 3 ^ 40 * 4391433 * 2
def baseEnd_4391433 : Nat := 2254915891015822231891673

theorem tailTrace_4391433 : CollatzResearch.WordTrace tailWord_4391433 prefixEnd_4391433 2254915891015822231891673 := by
  unfold tailWord_4391433
  simp only [CollatzResearch.WordTrace]
  refine ⟨160168719899595712891194953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106779146599730475260796635 160168719899595712891194953)
  ·
    refine ⟨120126539924696784668396215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160168719899595712891194953 120126539924696784668396215)
    ·
      refine ⟨180189809887045177002594323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120126539924696784668396215 180189809887045177002594323)
      ·
        refine ⟨270284714830567765503891485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180189809887045177002594323 270284714830567765503891485)
        ·
          refine ⟨101356768061462912063959307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 270284714830567765503891485 101356768061462912063959307)
          ·
            refine ⟨152035152092194368095938961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101356768061462912063959307 152035152092194368095938961)
            ·
              refine ⟨114026364069145776071954221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152035152092194368095938961 114026364069145776071954221)
              ·
                refine ⟨42759886525929666026982833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114026364069145776071954221 42759886525929666026982833)
                ·
                  refine ⟨32069914894447249520237125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42759886525929666026982833 32069914894447249520237125)
                  ·
                    refine ⟨6013109042708859285044461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32069914894447249520237125 6013109042708859285044461)
                    ·
                      refine ⟨2254915891015822231891673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6013109042708859285044461 2254915891015822231891673)
                      ·
                        rfl

theorem cell23_4391433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 4, 3].length) (baseStart_4391433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391433 prefixEnd_4391433 := by exact prefixLift 4391433
  have htrace : WordTrace (prefixWord ++ tailWord_4391433) baseStart_4391433 baseEnd_4391433 := by
    simpa [prefixWord, tailWord_4391433, baseEnd_4391433] using wordTrace_append hprefix tailTrace_4391433
  have hstable : (prefixWord ++ tailWord_4391433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391433).length < 2 ^ (prefixWord ++ tailWord_4391433).sum := by decide
  have hdescent : baseEnd_4391433 < baseStart_4391433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391443 : List Nat := [1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 4]
def baseStart_4391443 : Nat := 118140960795 + 4391443 * 2 ^ 59
def prefixEnd_4391443 : Nat := 4983230072969 + 3 ^ 40 * 4391443 * 2
def baseEnd_4391443 : Nat := 2254921025822367192766627

theorem tailTrace_4391443 : CollatzResearch.WordTrace tailWord_4391443 prefixEnd_4391443 2254921025822367192766627 := by
  unfold tailWord_4391443
  simp only [CollatzResearch.WordTrace]
  refine ⟨160169084629559484599058983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106779389753039656399372655 160169084629559484599058983)
  ·
    refine ⟨240253626944339226898588475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160169084629559484599058983 240253626944339226898588475)
    ·
      refine ⟨360380440416508840347882713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240253626944339226898588475 360380440416508840347882713)
      ·
        refine ⟨270285330312381630260912035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 360380440416508840347882713 270285330312381630260912035)
        ·
          refine ⟨405427995468572445391368053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270285330312381630260912035 405427995468572445391368053)
          ·
            refine ⟨38008874575178666755440755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 405427995468572445391368053 38008874575178666755440755)
            ·
              refine ⟨57013311862768000133161133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38008874575178666755440755 57013311862768000133161133)
              ·
                refine ⟨21379991948538000049935425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57013311862768000133161133 21379991948538000049935425)
                ·
                  refine ⟨16034993961403500037451569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21379991948538000049935425 16034993961403500037451569)
                  ·
                    refine ⟨12026245471052625028088677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16034993961403500037451569 12026245471052625028088677)
                    ·
                      refine ⟨2254921025822367192766627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12026245471052625028088677 2254921025822367192766627)
                      ·
                        rfl

theorem cell23_4391443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 4].length) (baseStart_4391443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391443 prefixEnd_4391443 := by exact prefixLift 4391443
  have htrace : WordTrace (prefixWord ++ tailWord_4391443) baseStart_4391443 baseEnd_4391443 := by
    simpa [prefixWord, tailWord_4391443, baseEnd_4391443] using wordTrace_append hprefix tailTrace_4391443
  have hstable : (prefixWord ++ tailWord_4391443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391443).length < 2 ^ (prefixWord ++ tailWord_4391443).sum := by decide
  have hdescent : baseEnd_4391443 < baseStart_4391443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391464 : List Nat := [2, 1, 5, 2, 1, 1, 1, 2, 4, 2, 2]
def baseStart_4391464 : Nat := 118140960795 + 4391464 * 2 ^ 59
def prefixEnd_4391464 : Nat := 4983230072969 + 3 ^ 40 * 4391464 * 2
def baseEnd_4391464 : Nat := 2254931808916111610604031

theorem tailTrace_4391464 : CollatzResearch.WordTrace tailWord_4391464 prefixEnd_4391464 2254931808916111610604031 := by
  unfold tailWord_4391464
  simp only [CollatzResearch.WordTrace]
  refine ⟨80084925281241702592786723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106779900374988936790382297 80084925281241702592786723)
  ·
    refine ⟨120127387921862553889180085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80084925281241702592786723 120127387921862553889180085)
    ·
      refine ⟨11261942617674614427110633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 120127387921862553889180085 11261942617674614427110633)
      ·
        refine ⟨8446456963255960820332975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11261942617674614427110633 8446456963255960820332975)
        ·
          refine ⟨12669685444883941230499463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8446456963255960820332975 12669685444883941230499463)
          ·
            refine ⟨19004528167325911845749195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12669685444883941230499463 19004528167325911845749195)
            ·
              refine ⟨28506792250988867768623793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19004528167325911845749195 28506792250988867768623793)
              ·
                refine ⟨21380094188241650826467845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28506792250988867768623793 21380094188241650826467845)
                ·
                  refine ⟨4008767660295309529962721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21380094188241650826467845 4008767660295309529962721)
                  ·
                    refine ⟨3006575745221482147472041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4008767660295309529962721 3006575745221482147472041)
                    ·
                      refine ⟨2254931808916111610604031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3006575745221482147472041 2254931808916111610604031)
                      ·
                        rfl

theorem cell23_4391464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_4391464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391464 prefixEnd_4391464 := by exact prefixLift 4391464
  have htrace : WordTrace (prefixWord ++ tailWord_4391464) baseStart_4391464 baseEnd_4391464 := by
    simpa [prefixWord, tailWord_4391464, baseEnd_4391464] using wordTrace_append hprefix tailTrace_4391464
  have hstable : (prefixWord ++ tailWord_4391464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391464).length < 2 ^ (prefixWord ++ tailWord_4391464).sum := by decide
  have hdescent : baseEnd_4391464 < baseStart_4391464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391487 : List Nat := [1, 1, 2, 2, 3, 2, 5, 2, 5]
def baseStart_4391487 : Nat := 118140960795 + 4391487 * 2 ^ 59
def prefixEnd_4391487 : Nat := 4983230072969 + 3 ^ 40 * 4391487 * 2
def baseEnd_4391487 : Nat := 250549290996796113401825

theorem tailTrace_4391487 : CollatzResearch.WordTrace tailWord_4391487 prefixEnd_4391487 250549290996796113401825 := by
  unfold tailWord_4391487
  simp only [CollatzResearch.WordTrace]
  refine ⟨160170689441400080113660715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106780459627600053409107143 160170689441400080113660715)
  ·
    refine ⟨240256034162100120170491073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160170689441400080113660715 240256034162100120170491073)
    ·
      refine ⟨180192025621575090127868305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240256034162100120170491073 180192025621575090127868305)
      ·
        refine ⟨135144019216181317595901229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180192025621575090127868305 135144019216181317595901229)
        ·
          refine ⟨50679007206067994098462961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135144019216181317595901229 50679007206067994098462961)
          ·
            refine ⟨38009255404550995573847221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50679007206067994098462961 38009255404550995573847221)
            ·
              refine ⟨3563367694176655835048177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38009255404550995573847221 3563367694176655835048177)
              ·
                refine ⟨2672525770632491876286133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3563367694176655835048177 2672525770632491876286133)
                ·
                  refine ⟨250549290996796113401825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2672525770632491876286133 250549290996796113401825)
                  ·
                    rfl

theorem cell23_4391487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 2, 5].length) (baseStart_4391487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391487 prefixEnd_4391487 := by exact prefixLift 4391487
  have htrace : WordTrace (prefixWord ++ tailWord_4391487) baseStart_4391487 baseEnd_4391487 := by
    simpa [prefixWord, tailWord_4391487, baseEnd_4391487] using wordTrace_append hprefix tailTrace_4391487
  have hstable : (prefixWord ++ tailWord_4391487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391487).length < 2 ^ (prefixWord ++ tailWord_4391487).sum := by decide
  have hdescent : baseEnd_4391487 < baseStart_4391487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391492 : List Nat := [2, 3, 5, 1, 2, 1, 2, 1, 2, 1, 3]
def baseStart_4391492 : Nat := 118140960795 + 4391492 * 2 ^ 59
def prefixEnd_4391492 : Nat := 4983230072969 + 3 ^ 40 * 4391492 * 2
def baseEnd_4391492 : Nat := 2254946186374437501053903

theorem tailTrace_4391492 : CollatzResearch.WordTrace tailWord_4391492 prefixEnd_4391492 2254946186374437501053903 := by
  unfold tailWord_4391492
  simp only [CollatzResearch.WordTrace]
  refine ⟨80085435903190982983796365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106780581204254643978395153 80085435903190982983796365)
  ·
    refine ⟨30032038463696618618923637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80085435903190982983796365 30032038463696618618923637)
    ·
      refine ⟨2815503605971557995524091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30032038463696618618923637 2815503605971557995524091)
      ·
        refine ⟨4223255408957336993286137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2815503605971557995524091 4223255408957336993286137)
        ·
          refine ⟨3167441556718002744964603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4223255408957336993286137 3167441556718002744964603)
          ·
            refine ⟨4751162335077004117446905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3167441556718002744964603 4751162335077004117446905)
            ·
              refine ⟨3563371751307753088085179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4751162335077004117446905 3563371751307753088085179)
              ·
                refine ⟨5345057626961629632127769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3563371751307753088085179 5345057626961629632127769)
                ·
                  refine ⟨4008793220221222224095827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5345057626961629632127769 4008793220221222224095827)
                  ·
                    refine ⟨6013189830331833336143741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4008793220221222224095827 6013189830331833336143741)
                    ·
                      refine ⟨2254946186374437501053903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6013189830331833336143741 2254946186374437501053903)
                      ·
                        rfl

theorem cell23_4391492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_4391492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391492 prefixEnd_4391492 := by exact prefixLift 4391492
  have htrace : WordTrace (prefixWord ++ tailWord_4391492) baseStart_4391492 baseEnd_4391492 := by
    simpa [prefixWord, tailWord_4391492, baseEnd_4391492] using wordTrace_append hprefix tailTrace_4391492
  have hstable : (prefixWord ++ tailWord_4391492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391492).length < 2 ^ (prefixWord ++ tailWord_4391492).sum := by decide
  have hdescent : baseEnd_4391492 < baseStart_4391492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391493 : List Nat := [1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 7]
def baseStart_4391493 : Nat := 118140960795 + 4391493 * 2 ^ 59
def prefixEnd_4391493 : Nat := 4983230072969 + 3 ^ 40 * 4391493 * 2
def baseEnd_4391493 : Nat := 2254946699855091997141397

theorem tailTrace_4391493 : CollatzResearch.WordTrace tailWord_4391493 prefixEnd_4391493 2254946699855091997141397 := by
  unfold tailWord_4391493
  simp only [CollatzResearch.WordTrace]
  refine ⟨160170908279378343138379133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106780605519585562092252755 160170908279378343138379133)
  ·
    refine ⟨60064090604766878676892175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160170908279378343138379133 60064090604766878676892175)
    ·
      refine ⟨90096135907150318015338263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60064090604766878676892175 90096135907150318015338263)
      ·
        refine ⟨135144203860725477023007395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90096135907150318015338263 135144203860725477023007395)
        ·
          refine ⟨202716305791088215534511093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135144203860725477023007395 202716305791088215534511093)
          ·
            refine ⟨19004653667914520206360415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 202716305791088215534511093 19004653667914520206360415)
            ·
              refine ⟨28506980501871780309540623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19004653667914520206360415 28506980501871780309540623)
              ·
                refine ⟨42760470752807670464310935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28506980501871780309540623 42760470752807670464310935)
                ·
                  refine ⟨64140706129211505696466403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42760470752807670464310935 64140706129211505696466403)
                  ·
                    refine ⟨96211059193817258544699605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 64140706129211505696466403 96211059193817258544699605)
                    ·
                      refine ⟨2254946699855091997141397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 96211059193817258544699605 2254946699855091997141397)
                      ·
                        rfl

theorem cell23_4391493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 7].length) (baseStart_4391493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391493 prefixEnd_4391493 := by exact prefixLift 4391493
  have htrace : WordTrace (prefixWord ++ tailWord_4391493) baseStart_4391493 baseEnd_4391493 := by
    simpa [prefixWord, tailWord_4391493, baseEnd_4391493] using wordTrace_append hprefix tailTrace_4391493
  have hstable : (prefixWord ++ tailWord_4391493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391493).length < 2 ^ (prefixWord ++ tailWord_4391493).sum := by decide
  have hdescent : baseEnd_4391493 < baseStart_4391493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391503 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 4]
def baseStart_4391503 : Nat := 118140960795 + 4391503 * 2 ^ 59
def prefixEnd_4391503 : Nat := 4983230072969 + 3 ^ 40 * 4391503 * 2
def baseEnd_4391503 : Nat := 2254951834661636958016351

theorem tailTrace_4391503 : CollatzResearch.WordTrace tailWord_4391503 prefixEnd_4391503 2254951834661636958016351 := by
  unfold tailWord_4391503
  simp only [CollatzResearch.WordTrace]
  refine ⟨160171273009342114846243163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106780848672894743230828775 160171273009342114846243163)
  ·
    refine ⟨240256909514013172269364745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160171273009342114846243163 240256909514013172269364745)
    ·
      refine ⟨180192682135509879202023559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240256909514013172269364745 180192682135509879202023559)
      ·
        refine ⟨270289023203264818803035339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180192682135509879202023559 270289023203264818803035339)
        ·
          refine ⟨405433534804897228204553009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270289023203264818803035339 405433534804897228204553009)
          ·
            refine ⟨304075151103672921153414757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 405433534804897228204553009 304075151103672921153414757)
            ·
              refine ⟨57014090831938672716265267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 304075151103672921153414757 57014090831938672716265267)
              ·
                refine ⟨85521136247908009074397901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57014090831938672716265267 85521136247908009074397901)
                ·
                  refine ⟨32070426092965503402899213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85521136247908009074397901 32070426092965503402899213)
                  ·
                    refine ⟨12026409784862063776087205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32070426092965503402899213 12026409784862063776087205)
                    ·
                      refine ⟨2254951834661636958016351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12026409784862063776087205 2254951834661636958016351)
                      ·
                        rfl

theorem cell23_4391503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 4].length) (baseStart_4391503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391503 prefixEnd_4391503 := by exact prefixLift 4391503
  have htrace : WordTrace (prefixWord ++ tailWord_4391503) baseStart_4391503 baseEnd_4391503 := by
    simpa [prefixWord, tailWord_4391503, baseEnd_4391503] using wordTrace_append hprefix tailTrace_4391503
  have hstable : (prefixWord ++ tailWord_4391503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391503).length < 2 ^ (prefixWord ++ tailWord_4391503).sum := by decide
  have hdescent : baseEnd_4391503 < baseStart_4391503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391520 : List Nat := [2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 4]
def baseStart_4391520 : Nat := 118140960795 + 4391520 * 2 ^ 59
def prefixEnd_4391520 : Nat := 4983230072969 + 3 ^ 40 * 4391520 * 2
def baseEnd_4391520 : Nat := 2254960563832763391503773

theorem tailTrace_4391520 : CollatzResearch.WordTrace tailWord_4391520 prefixEnd_4391520 2254960563832763391503773 := by
  unfold tailWord_4391520
  simp only [CollatzResearch.WordTrace]
  refine ⟨80085946525140263374806007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106781262033520351166408009 80085946525140263374806007)
  ·
    refine ⟨120128919787710395062209011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80085946525140263374806007 120128919787710395062209011)
    ·
      refine ⟨180193379681565592593313517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120128919787710395062209011 180193379681565592593313517)
      ·
        refine ⟨67572517380587097222492569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 180193379681565592593313517 67572517380587097222492569)
        ·
          refine ⟨50679388035440322916869427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67572517380587097222492569 50679388035440322916869427)
          ·
            refine ⟨76019082053160484375304141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50679388035440322916869427 76019082053160484375304141)
            ·
              refine ⟨28507155769935181640739053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76019082053160484375304141 28507155769935181640739053)
              ·
                refine ⟨10690183413725693115277145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28507155769935181640739053 10690183413725693115277145)
                ·
                  refine ⟨8017637560294269836457859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10690183413725693115277145 8017637560294269836457859)
                  ·
                    refine ⟨12026456340441404754686789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8017637560294269836457859 12026456340441404754686789)
                    ·
                      refine ⟨2254960563832763391503773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12026456340441404754686789 2254960563832763391503773)
                      ·
                        rfl

theorem cell23_4391520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_4391520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391520 prefixEnd_4391520 := by exact prefixLift 4391520
  have htrace : WordTrace (prefixWord ++ tailWord_4391520) baseStart_4391520 baseEnd_4391520 := by
    simpa [prefixWord, tailWord_4391520, baseEnd_4391520] using wordTrace_append hprefix tailTrace_4391520
  have hstable : (prefixWord ++ tailWord_4391520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391520).length < 2 ^ (prefixWord ++ tailWord_4391520).sum := by decide
  have hdescent : baseEnd_4391520 < baseStart_4391520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391543 : List Nat := [1, 1, 3, 1, 1, 3, 2, 3, 8]
def baseStart_4391543 : Nat := 118140960795 + 4391543 * 2 ^ 59
def prefixEnd_4391543 : Nat := 4983230072969 + 3 ^ 40 * 4391543 * 2
def baseEnd_4391543 : Nat := 250552485987535200168463

theorem tailTrace_4391543 : CollatzResearch.WordTrace tailWord_4391543 prefixEnd_4391543 250552485987535200168463 := by
  unfold tailWord_4391543
  simp only [CollatzResearch.WordTrace]
  refine ⟨160172731929197201677699283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106781821286131467785132855 160172731929197201677699283)
  ·
    refine ⟨240259097893795802516548925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160172731929197201677699283 240259097893795802516548925)
    ·
      refine ⟨90097161710173425943705847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 240259097893795802516548925 90097161710173425943705847)
      ·
        refine ⟨135145742565260138915558771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90097161710173425943705847 135145742565260138915558771)
        ·
          refine ⟨202718613847890208373338157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135145742565260138915558771 202718613847890208373338157)
          ·
            refine ⟨76019480192958828140001809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 202718613847890208373338157 76019480192958828140001809)
            ·
              refine ⟨57014610144719121105001357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76019480192958828140001809 57014610144719121105001357)
              ·
                refine ⟨21380478804269670414375509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57014610144719121105001357 21380478804269670414375509)
                ·
                  refine ⟨250552485987535200168463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21380478804269670414375509 250552485987535200168463)
                  ·
                    rfl

theorem cell23_4391543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 8].length) (baseStart_4391543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391543 prefixEnd_4391543 := by exact prefixLift 4391543
  have htrace : WordTrace (prefixWord ++ tailWord_4391543) baseStart_4391543 baseEnd_4391543 := by
    simpa [prefixWord, tailWord_4391543, baseEnd_4391543] using wordTrace_append hprefix tailTrace_4391543
  have hstable : (prefixWord ++ tailWord_4391543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391543).length < 2 ^ (prefixWord ++ tailWord_4391543).sum := by decide
  have hdescent : baseEnd_4391543 < baseStart_4391543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391563 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 6]
def baseStart_4391563 : Nat := 118140960795 + 4391563 * 2 ^ 59
def prefixEnd_4391563 : Nat := 4983230072969 + 3 ^ 40 * 4391563 * 2
def baseEnd_4391563 : Nat := 2254982643500906723266075

theorem tailTrace_4391563 : CollatzResearch.WordTrace tailWord_4391563 prefixEnd_4391563 2254982643500906723266075 := by
  unfold tailWord_4391563
  simp only [CollatzResearch.WordTrace]
  refine ⟨160173461389124745093427343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106782307592749830062284895 160173461389124745093427343)
  ·
    refine ⟨240260192083687117640141015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160173461389124745093427343 240260192083687117640141015)
    ·
      refine ⟨360390288125530676460211523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240260192083687117640141015 360390288125530676460211523)
      ·
        refine ⟨540585432188296014690317285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 360390288125530676460211523 540585432188296014690317285)
        ·
          refine ⟨101359768535305502754434491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 540585432188296014690317285 101359768535305502754434491)
          ·
            refine ⟨152039652802958254131651737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101359768535305502754434491 152039652802958254131651737)
            ·
              refine ⟨114029739602218690598738803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152039652802958254131651737 114029739602218690598738803)
              ·
                refine ⟨171044609403328035898108205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114029739602218690598738803 171044609403328035898108205)
                ·
                  refine ⟨64141728526248013461790577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 171044609403328035898108205 64141728526248013461790577)
                  ·
                    refine ⟨48106296394686010096342933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64141728526248013461790577 48106296394686010096342933)
                    ·
                      refine ⟨2254982643500906723266075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48106296394686010096342933 2254982643500906723266075)
                      ·
                        rfl

theorem cell23_4391563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 6].length) (baseStart_4391563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391563 prefixEnd_4391563 := by exact prefixLift 4391563
  have htrace : WordTrace (prefixWord ++ tailWord_4391563) baseStart_4391563 baseEnd_4391563 := by
    simpa [prefixWord, tailWord_4391563, baseEnd_4391563] using wordTrace_append hprefix tailTrace_4391563
  have hstable : (prefixWord ++ tailWord_4391563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391563).length < 2 ^ (prefixWord ++ tailWord_4391563).sum := by decide
  have hdescent : baseEnd_4391563 < baseStart_4391563 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391594 : List Nat := [3, 1, 5, 2, 1, 1, 1, 1, 8]
def baseStart_4391594 : Nat := 118140960795 + 4391594 * 2 ^ 59
def prefixEnd_4391594 : Nat := 4983230072969 + 3 ^ 40 * 4391594 * 2
def baseEnd_4391594 : Nat := 250555395711244011330937

theorem tailTrace_4391594 : CollatzResearch.WordTrace tailWord_4391594 prefixEnd_4391594 250555395711244011330937 := by
  unfold tailWord_4391594
  simp only [CollatzResearch.WordTrace]
  refine ⟨40043648013003109346951459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106783061368008291591870557 40043648013003109346951459)
  ·
    refine ⟨60065472019504664020427189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40043648013003109346951459 60065472019504664020427189)
    ·
      refine ⟨5631138001828562251915049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60065472019504664020427189 5631138001828562251915049)
      ·
        refine ⟨4223353501371421688936287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5631138001828562251915049 4223353501371421688936287)
        ·
          refine ⟨6335030252057132533404431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4223353501371421688936287 6335030252057132533404431)
          ·
            refine ⟨9502545378085698800106647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6335030252057132533404431 9502545378085698800106647)
            ·
              refine ⟨14253818067128548200159971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9502545378085698800106647 14253818067128548200159971)
              ·
                refine ⟨21380727100692822300239957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14253818067128548200159971 21380727100692822300239957)
                ·
                  refine ⟨250555395711244011330937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21380727100692822300239957 250555395711244011330937)
                  ·
                    rfl

theorem cell23_4391594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 8].length) (baseStart_4391594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391594 prefixEnd_4391594 := by exact prefixLift 4391594
  have htrace : WordTrace (prefixWord ++ tailWord_4391594) baseStart_4391594 baseEnd_4391594 := by
    simpa [prefixWord, tailWord_4391594, baseEnd_4391594] using wordTrace_append hprefix tailTrace_4391594
  have hstable : (prefixWord ++ tailWord_4391594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391594).length < 2 ^ (prefixWord ++ tailWord_4391594).sum := by decide
  have hdescent : baseEnd_4391594 < baseStart_4391594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391647 : List Nat := [1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 5]
def baseStart_4391647 : Nat := 118140960795 + 4391647 * 2 ^ 59
def prefixEnd_4391647 : Nat := 4983230072969 + 3 ^ 40 * 4391647 * 2
def baseEnd_4391647 : Nat := 2255025775875884394615689

theorem tailTrace_4391647 : CollatzResearch.WordTrace tailWord_4391647 prefixEnd_4391647 2255025775875884394615689 := by
  unfold tailWord_4391647
  simp only [CollatzResearch.WordTrace]
  refine ⟨160176525120820427439485195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106784350080546951626323463 160176525120820427439485195)
  ·
    refine ⟨240264787681230641159227793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160176525120820427439485195 240264787681230641159227793)
    ·
      refine ⟨180198590760922980869420845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240264787681230641159227793 180198590760922980869420845)
      ·
        refine ⟨67574471535346117826032817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 180198590760922980869420845 67574471535346117826032817)
        ·
          refine ⟨50680853651509588369524613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67574471535346117826032817 50680853651509588369524613)
          ·
            refine ⟨9502660059658047819285865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50680853651509588369524613 9502660059658047819285865)
            ·
              refine ⟨7126995044743535864464399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9502660059658047819285865 7126995044743535864464399)
              ·
                refine ⟨10690492567115303796696599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7126995044743535864464399 10690492567115303796696599)
                ·
                  refine ⟨16035738850672955695044899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10690492567115303796696599 16035738850672955695044899)
                  ·
                    refine ⟨24053608276009433542567349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16035738850672955695044899 24053608276009433542567349)
                    ·
                      refine ⟨2255025775875884394615689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24053608276009433542567349 2255025775875884394615689)
                      ·
                        rfl

theorem cell23_4391647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 5].length) (baseStart_4391647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391647 prefixEnd_4391647 := by exact prefixLift 4391647
  have htrace : WordTrace (prefixWord ++ tailWord_4391647) baseStart_4391647 baseEnd_4391647 := by
    simpa [prefixWord, tailWord_4391647, baseEnd_4391647] using wordTrace_append hprefix tailTrace_4391647
  have hstable : (prefixWord ++ tailWord_4391647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391647).length < 2 ^ (prefixWord ++ tailWord_4391647).sum := by decide
  have hdescent : baseEnd_4391647 < baseStart_4391647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391677 : List Nat := [1, 4, 1, 1, 1, 1, 4, 3, 1, 3, 3]
def baseStart_4391677 : Nat := 118140960795 + 4391677 * 2 ^ 59
def prefixEnd_4391677 : Nat := 4983230072969 + 3 ^ 40 * 4391677 * 2
def baseEnd_4391677 : Nat := 2255041180295519277240551

theorem tailTrace_4391677 : CollatzResearch.WordTrace tailWord_4391677 prefixEnd_4391677 2255041180295519277240551 := by
  unfold tailWord_4391677
  simp only [CollatzResearch.WordTrace]
  refine ⟨160177619310711742563077285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106785079540474495042051523 160177619310711742563077285)
  ·
    refine ⟨30033303620758451730576991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160177619310711742563077285 30033303620758451730576991)
    ·
      refine ⟨45049955431137677595865487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30033303620758451730576991 45049955431137677595865487)
      ·
        refine ⟨67574933146706516393798231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45049955431137677595865487 67574933146706516393798231)
        ·
          refine ⟨101362399720059774590697347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67574933146706516393798231 101362399720059774590697347)
          ·
            refine ⟨152043599580089661886046021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101362399720059774590697347 152043599580089661886046021)
            ·
              refine ⟨28508174921266811603633629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 152043599580089661886046021 28508174921266811603633629)
              ·
                refine ⟨10690565595475054351362611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28508174921266811603633629 10690565595475054351362611)
                ·
                  refine ⟨16035848393212581527043917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10690565595475054351362611 16035848393212581527043917)
                  ·
                    refine ⟨6013443147454718072641469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16035848393212581527043917 6013443147454718072641469)
                    ·
                      refine ⟨2255041180295519277240551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6013443147454718072641469 2255041180295519277240551)
                      ·
                        rfl

theorem cell23_4391677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 1, 3, 3].length) (baseStart_4391677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391677 prefixEnd_4391677 := by exact prefixLift 4391677
  have htrace : WordTrace (prefixWord ++ tailWord_4391677) baseStart_4391677 baseEnd_4391677 := by
    simpa [prefixWord, tailWord_4391677, baseEnd_4391677] using wordTrace_append hprefix tailTrace_4391677
  have hstable : (prefixWord ++ tailWord_4391677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391677).length < 2 ^ (prefixWord ++ tailWord_4391677).sum := by decide
  have hdescent : baseEnd_4391677 < baseStart_4391677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391698 : List Nat := [3, 2, 4, 1, 3, 1, 1, 1, 1, 1, 5]
def baseStart_4391698 : Nat := 118140960795 + 4391698 * 2 ^ 59
def prefixEnd_4391698 : Nat := 4983230072969 + 3 ^ 40 * 4391698 * 2
def baseEnd_4391698 : Nat := 2255051963389263695077955

theorem tailTrace_4391698 : CollatzResearch.WordTrace tailWord_4391698 prefixEnd_4391698 2255051963389263695077955 := by
  unfold tailWord_4391698
  simp only [CollatzResearch.WordTrace]
  refine ⟨40044596310908915787397937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106785590162423775433061165 40044596310908915787397937)
  ·
    refine ⟨30033447233181686840548453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40044596310908915787397937 30033447233181686840548453)
    ·
      refine ⟨5631271356221566282602835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30033447233181686840548453 5631271356221566282602835)
      ·
        refine ⟨8446907034332349423904253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5631271356221566282602835 8446907034332349423904253)
        ·
          refine ⟨3167590137874631033964095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8446907034332349423904253 3167590137874631033964095)
          ·
            refine ⟨4751385206811946550946143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3167590137874631033964095 4751385206811946550946143)
            ·
              refine ⟨7127077810217919826419215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4751385206811946550946143 7127077810217919826419215)
              ·
                refine ⟨10690616715326879739628823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7127077810217919826419215 10690616715326879739628823)
                ·
                  refine ⟨16035925072990319609443235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10690616715326879739628823 16035925072990319609443235)
                  ·
                    refine ⟨24053887609485479414164853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16035925072990319609443235 24053887609485479414164853)
                    ·
                      refine ⟨2255051963389263695077955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24053887609485479414164853 2255051963389263695077955)
                      ·
                        rfl

theorem cell23_4391698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_4391698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391698 prefixEnd_4391698 := by exact prefixLift 4391698
  have htrace : WordTrace (prefixWord ++ tailWord_4391698) baseStart_4391698 baseEnd_4391698 := by
    simpa [prefixWord, tailWord_4391698, baseEnd_4391698] using wordTrace_append hprefix tailTrace_4391698
  have hstable : (prefixWord ++ tailWord_4391698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391698).length < 2 ^ (prefixWord ++ tailWord_4391698).sum := by decide
  have hdescent : baseEnd_4391698 < baseStart_4391698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391711 : List Nat := [1, 1, 2, 4, 2, 3, 2, 2, 2, 1, 3]
def baseStart_4391711 : Nat := 118140960795 + 4391711 * 2 ^ 59
def prefixEnd_4391711 : Nat := 4983230072969 + 3 ^ 40 * 4391711 * 2
def baseEnd_4391711 : Nat := 2255058638637772144215395

theorem tailTrace_4391711 : CollatzResearch.WordTrace tailWord_4391711 prefixEnd_4391711 2255058638637772144215395 := by
  unfold tailWord_4391711
  simp only [CollatzResearch.WordTrace]
  refine ⟨160178859392588566369814987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106785906261725710913209991 160178859392588566369814987)
  ·
    refine ⟨240268289088882849554722481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160178859392588566369814987 240268289088882849554722481)
    ·
      refine ⟨180201216816662137166041861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240268289088882849554722481 180201216816662137166041861)
      ·
        refine ⟨33787728153124150718632849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 180201216816662137166041861 33787728153124150718632849)
        ·
          refine ⟨25340796114843113038974637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33787728153124150718632849 25340796114843113038974637)
          ·
            refine ⟨9502798543066167389615489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25340796114843113038974637 9502798543066167389615489)
            ·
              refine ⟨7127098907299625542211617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9502798543066167389615489 7127098907299625542211617)
              ·
                refine ⟨5345324180474719156658713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7127098907299625542211617 5345324180474719156658713)
                ·
                  refine ⟨4008993135356039367494035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5345324180474719156658713 4008993135356039367494035)
                  ·
                    refine ⟨6013489703034059051241053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4008993135356039367494035 6013489703034059051241053)
                    ·
                      refine ⟨2255058638637772144215395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6013489703034059051241053 2255058638637772144215395)
                      ·
                        rfl

theorem cell23_4391711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_4391711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391711 prefixEnd_4391711 := by exact prefixLift 4391711
  have htrace : WordTrace (prefixWord ++ tailWord_4391711) baseStart_4391711 baseEnd_4391711 := by
    simpa [prefixWord, tailWord_4391711, baseEnd_4391711] using wordTrace_append hprefix tailTrace_4391711
  have hstable : (prefixWord ++ tailWord_4391711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391711).length < 2 ^ (prefixWord ++ tailWord_4391711).sum := by decide
  have hdescent : baseEnd_4391711 < baseStart_4391711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391784 : List Nat := [2, 1, 4, 2, 1, 2, 2, 1, 2, 3, 3]
def baseStart_4391784 : Nat := 118140960795 + 4391784 * 2 ^ 59
def prefixEnd_4391784 : Nat := 4983230072969 + 3 ^ 40 * 4391784 * 2
def baseEnd_4391784 : Nat := 2255096122725550358602559

theorem tailTrace_4391784 : CollatzResearch.WordTrace tailWord_4391784 prefixEnd_4391784 2255096122725550358602559 := by
  unfold tailWord_4391784
  simp only [CollatzResearch.WordTrace]
  refine ⟨80090760960662049918611203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106787681280882733224814937 80090760960662049918611203)
  ·
    refine ⟨120136141440993074877916805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80090760960662049918611203 120136141440993074877916805)
    ·
      refine ⟨22525526520186201539609401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120136141440993074877916805 22525526520186201539609401)
      ·
        refine ⟨16894144890139651154707051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22525526520186201539609401 16894144890139651154707051)
        ·
          refine ⟨25341217335209476732060577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16894144890139651154707051 25341217335209476732060577)
          ·
            refine ⟨19005913001407107549045433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25341217335209476732060577 19005913001407107549045433)
            ·
              refine ⟨14254434751055330661784075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19005913001407107549045433 14254434751055330661784075)
              ·
                refine ⟨21381652126582995992676113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14254434751055330661784075 21381652126582995992676113)
                ·
                  refine ⟨16036239094937246994507085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21381652126582995992676113 16036239094937246994507085)
                  ·
                    refine ⟨6013589660601467622940157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16036239094937246994507085 6013589660601467622940157)
                    ·
                      refine ⟨2255096122725550358602559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6013589660601467622940157 2255096122725550358602559)
                      ·
                        rfl

theorem cell23_4391784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_4391784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391784 prefixEnd_4391784 := by exact prefixLift 4391784
  have htrace : WordTrace (prefixWord ++ tailWord_4391784) baseStart_4391784 baseEnd_4391784 := by
    simpa [prefixWord, tailWord_4391784, baseEnd_4391784] using wordTrace_append hprefix tailTrace_4391784
  have hstable : (prefixWord ++ tailWord_4391784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391784).length < 2 ^ (prefixWord ++ tailWord_4391784).sum := by decide
  have hdescent : baseEnd_4391784 < baseStart_4391784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391794 : List Nat := [3, 2, 1, 2, 1, 1, 2, 2, 2, 5, 2]
def baseStart_4391794 : Nat := 118140960795 + 4391794 * 2 ^ 59
def prefixEnd_4391794 : Nat := 4983230072969 + 3 ^ 40 * 4391794 * 2
def baseEnd_4391794 : Nat := 2255101257532095319477513

theorem tailTrace_4391794 : CollatzResearch.WordTrace tailWord_4391794 prefixEnd_4391794 2255101257532095319477513 := by
  unfold tailWord_4391794
  simp only [CollatzResearch.WordTrace]
  refine ⟨40045471662821967886271609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106787924434191914363390957 40045471662821967886271609)
  ·
    refine ⟨30034103747116475914703707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40045471662821967886271609 30034103747116475914703707)
    ·
      refine ⟨45051155620674713872055561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30034103747116475914703707 45051155620674713872055561)
      ·
        refine ⟨33788366715506035404041671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45051155620674713872055561 33788366715506035404041671)
        ·
          refine ⟨50682550073259053106062507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33788366715506035404041671 50682550073259053106062507)
          ·
            refine ⟨76023825109888579659093761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50682550073259053106062507 76023825109888579659093761)
            ·
              refine ⟨57017868832416434744320321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76023825109888579659093761 57017868832416434744320321)
              ·
                refine ⟨42763401624312326058240241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57017868832416434744320321 42763401624312326058240241)
                ·
                  refine ⟨32072551218234244543680181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42763401624312326058240241 32072551218234244543680181)
                  ·
                    refine ⟨3006801676709460425970017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32072551218234244543680181 3006801676709460425970017)
                    ·
                      refine ⟨2255101257532095319477513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3006801676709460425970017 2255101257532095319477513)
                      ·
                        rfl

theorem cell23_4391794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_4391794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391794 prefixEnd_4391794 := by exact prefixLift 4391794
  have htrace : WordTrace (prefixWord ++ tailWord_4391794) baseStart_4391794 baseEnd_4391794 := by
    simpa [prefixWord, tailWord_4391794, baseEnd_4391794] using wordTrace_append hprefix tailTrace_4391794
  have hstable : (prefixWord ++ tailWord_4391794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391794).length < 2 ^ (prefixWord ++ tailWord_4391794).sum := by decide
  have hdescent : baseEnd_4391794 < baseStart_4391794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391807 : List Nat := [1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 4]
def baseStart_4391807 : Nat := 118140960795 + 4391807 * 2 ^ 59
def prefixEnd_4391807 : Nat := 4983230072969 + 3 ^ 40 * 4391807 * 2
def baseEnd_4391807 : Nat := 2255107932780603768614953

theorem tailTrace_4391807 : CollatzResearch.WordTrace tailWord_4391807 prefixEnd_4391807 2255107932780603768614953 := by
  unfold tailWord_4391807
  simp only [CollatzResearch.WordTrace]
  refine ⟨160182360800240774765309675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106788240533493849843539783 160182360800240774765309675)
  ·
    refine ⟨240273541200361162147964513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160182360800240774765309675 240273541200361162147964513)
    ·
      refine ⟨180205155900270871610973385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240273541200361162147964513 180205155900270871610973385)
      ·
        refine ⟨135153866925203153708230039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180205155900270871610973385 135153866925203153708230039)
        ·
          refine ⟨202730800387804730562345059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135153866925203153708230039 202730800387804730562345059)
          ·
            refine ⟨304096200581707095843517589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202730800387804730562345059 304096200581707095843517589)
            ·
              refine ⟨14254509402267520117664887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 304096200581707095843517589 14254509402267520117664887)
              ·
                refine ⟨21381764103401280176497331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14254509402267520117664887 21381764103401280176497331)
                ·
                  refine ⟨32072646155101920264745997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21381764103401280176497331 32072646155101920264745997)
                  ·
                    refine ⟨12027242308163220099279749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32072646155101920264745997 12027242308163220099279749)
                    ·
                      refine ⟨2255107932780603768614953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12027242308163220099279749 2255107932780603768614953)
                      ·
                        rfl

theorem cell23_4391807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 4].length) (baseStart_4391807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391807 prefixEnd_4391807 := by exact prefixLift 4391807
  have htrace : WordTrace (prefixWord ++ tailWord_4391807) baseStart_4391807 baseEnd_4391807 := by
    simpa [prefixWord, tailWord_4391807, baseEnd_4391807] using wordTrace_append hprefix tailTrace_4391807
  have hstable : (prefixWord ++ tailWord_4391807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391807).length < 2 ^ (prefixWord ++ tailWord_4391807).sum := by decide
  have hdescent : baseEnd_4391807 < baseStart_4391807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391827 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 3, 4, 3]
def baseStart_4391827 : Nat := 118140960795 + 4391827 * 2 ^ 59
def prefixEnd_4391827 : Nat := 4983230072969 + 3 ^ 40 * 4391827 * 2
def baseEnd_4391827 : Nat := 2255118202393693690364861

theorem tailTrace_4391827 : CollatzResearch.WordTrace tailWord_4391827 prefixEnd_4391827 2255118202393693690364861 := by
  unfold tailWord_4391827
  simp only [CollatzResearch.WordTrace]
  refine ⟨160183090260168318181037735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106788726840112212120691823 160183090260168318181037735)
  ·
    refine ⟨240274635390252477271556603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160183090260168318181037735 240274635390252477271556603)
    ·
      refine ⟨360411953085378715907334905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240274635390252477271556603 360411953085378715907334905)
      ·
        refine ⟨270308964814034036930501179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 360411953085378715907334905 270308964814034036930501179)
        ·
          refine ⟨405463447221051055395751769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270308964814034036930501179 405463447221051055395751769)
          ·
            refine ⟨304097585415788291546813827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 405463447221051055395751769 304097585415788291546813827)
            ·
              refine ⟨456146378123682437320220741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304097585415788291546813827 456146378123682437320220741)
              ·
                refine ⟨85527445898190456997541389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 456146378123682437320220741 85527445898190456997541389)
                ·
                  refine ⟨32072792211821421374078021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85527445898190456997541389 32072792211821421374078021)
                  ·
                    refine ⟨6013648539716516507639629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32072792211821421374078021 6013648539716516507639629)
                    ·
                      refine ⟨2255118202393693690364861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6013648539716516507639629 2255118202393693690364861)
                      ·
                        rfl

theorem cell23_4391827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 4, 3].length) (baseStart_4391827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391827 prefixEnd_4391827 := by exact prefixLift 4391827
  have htrace : WordTrace (prefixWord ++ tailWord_4391827) baseStart_4391827 baseEnd_4391827 := by
    simpa [prefixWord, tailWord_4391827, baseEnd_4391827] using wordTrace_append hprefix tailTrace_4391827
  have hstable : (prefixWord ++ tailWord_4391827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391827).length < 2 ^ (prefixWord ++ tailWord_4391827).sum := by decide
  have hdescent : baseEnd_4391827 < baseStart_4391827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391844 : List Nat := [2, 3, 1, 2, 1, 2, 1, 2, 4, 2, 3]
def baseStart_4391844 : Nat := 118140960795 + 4391844 * 2 ^ 59
def prefixEnd_4391844 : Nat := 4983230072969 + 3 ^ 40 * 4391844 * 2
def baseEnd_4391844 : Nat := 2255126931564820123852283

theorem tailTrace_4391844 : CollatzResearch.WordTrace tailWord_4391844 prefixEnd_4391844 2255126931564820123852283 := by
  unfold tailWord_4391844
  simp only [CollatzResearch.WordTrace]
  refine ⟨80091855150553365042203293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106789140200737820056271057 80091855150553365042203293)
  ·
    refine ⟨30034445681457511890826235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80091855150553365042203293 30034445681457511890826235)
    ·
      refine ⟨45051668522186267836239353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30034445681457511890826235 45051668522186267836239353)
      ·
        refine ⟨33788751391639700877179515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45051668522186267836239353 33788751391639700877179515)
        ·
          refine ⟨50683127087459551315769273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33788751391639700877179515 50683127087459551315769273)
          ·
            refine ⟨38012345315594663486826955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50683127087459551315769273 38012345315594663486826955)
            ·
              refine ⟨57018517973391995230240433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38012345315594663486826955 57018517973391995230240433)
              ·
                refine ⟨42763888480043996422680325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57018517973391995230240433 42763888480043996422680325)
                ·
                  refine ⟨8018229090008249329252561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42763888480043996422680325 8018229090008249329252561)
                  ·
                    refine ⟨6013671817506186996939421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8018229090008249329252561 6013671817506186996939421)
                    ·
                      refine ⟨2255126931564820123852283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6013671817506186996939421 2255126931564820123852283)
                      ·
                        rfl

theorem cell23_4391844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_4391844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391844 prefixEnd_4391844 := by exact prefixLift 4391844
  have htrace : WordTrace (prefixWord ++ tailWord_4391844) baseStart_4391844 baseEnd_4391844 := by
    simpa [prefixWord, tailWord_4391844, baseEnd_4391844] using wordTrace_append hprefix tailTrace_4391844
  have hstable : (prefixWord ++ tailWord_4391844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391844).length < 2 ^ (prefixWord ++ tailWord_4391844).sum := by decide
  have hdescent : baseEnd_4391844 < baseStart_4391844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391861 : List Nat := [1, 3, 3, 2, 1, 1, 4, 1, 2, 2, 3]
def baseStart_4391861 : Nat := 118140960795 + 4391861 * 2 ^ 59
def prefixEnd_4391861 : Nat := 4983230072969 + 3 ^ 40 * 4391861 * 2
def baseEnd_4391861 : Nat := 2255135660735946557339705

theorem tailTrace_4391861 : CollatzResearch.WordTrace tailWord_4391861 prefixEnd_4391861 2255135660735946557339705 := by
  unfold tailWord_4391861
  simp only [CollatzResearch.WordTrace]
  refine ⟨160184330342045141987775437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106789553561363427991850291 160184330342045141987775437)
  ·
    refine ⟨60069123878266928245415789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160184330342045141987775437 60069123878266928245415789)
    ·
      refine ⟨22525921454350098092030921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60069123878266928245415789 22525921454350098092030921)
      ·
        refine ⟨16894441090762573569023191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22525921454350098092030921 16894441090762573569023191)
        ·
          refine ⟨25341661636143860353534787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16894441090762573569023191 25341661636143860353534787)
          ·
            refine ⟨38012492454215790530302181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25341661636143860353534787 38012492454215790530302181)
            ·
              refine ⟨7127342335165460724431659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38012492454215790530302181 7127342335165460724431659)
              ·
                refine ⟨10691013502748191086647489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7127342335165460724431659 10691013502748191086647489)
                ·
                  refine ⟨8018260127061143314985617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10691013502748191086647489 8018260127061143314985617)
                  ·
                    refine ⟨6013695095295857486239213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8018260127061143314985617 6013695095295857486239213)
                    ·
                      refine ⟨2255135660735946557339705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6013695095295857486239213 2255135660735946557339705)
                      ·
                        rfl

theorem cell23_4391861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_4391861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391861 prefixEnd_4391861 := by exact prefixLift 4391861
  have htrace : WordTrace (prefixWord ++ tailWord_4391861) baseStart_4391861 baseEnd_4391861 := by
    simpa [prefixWord, tailWord_4391861, baseEnd_4391861] using wordTrace_append hprefix tailTrace_4391861
  have hstable : (prefixWord ++ tailWord_4391861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391861).length < 2 ^ (prefixWord ++ tailWord_4391861).sum := by decide
  have hdescent : baseEnd_4391861 < baseStart_4391861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391918 : List Nat := [4, 1, 2, 1, 4, 1, 1, 1, 1, 5, 2]
def baseStart_4391918 : Nat := 118140960795 + 4391918 * 2 ^ 59
def prefixEnd_4391918 : Nat := 4983230072969 + 3 ^ 40 * 4391918 * 2
def baseEnd_4391918 : Nat := 2255164929133252834326943

theorem tailTrace_4391918 : CollatzResearch.WordTrace tailWord_4391918 prefixEnd_4391918 2255164929133252834326943 := by
  unfold tailWord_4391918
  simp only [CollatzResearch.WordTrace]
  refine ⟨20023301162854830090325051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106790939535225760481733605 20023301162854830090325051)
  ·
    refine ⟨30034951744282245135487577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20023301162854830090325051 30034951744282245135487577)
    ·
      refine ⟨22526213808211683851615683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30034951744282245135487577 22526213808211683851615683)
      ·
        refine ⟨33789320712317525777423525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22526213808211683851615683 33789320712317525777423525)
        ·
          refine ⟨6335497633559536083266911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33789320712317525777423525 6335497633559536083266911)
          ·
            refine ⟨9503246450339304124900367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6335497633559536083266911 9503246450339304124900367)
            ·
              refine ⟨14254869675508956187350551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9503246450339304124900367 14254869675508956187350551)
              ·
                refine ⟨21382304513263434281025827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14254869675508956187350551 21382304513263434281025827)
                ·
                  refine ⟨32073456769895151421538741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21382304513263434281025827 32073456769895151421538741)
                  ·
                    refine ⟨3006886572177670445769257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32073456769895151421538741 3006886572177670445769257)
                    ·
                      refine ⟨2255164929133252834326943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3006886572177670445769257 2255164929133252834326943)
                      ·
                        rfl

theorem cell23_4391918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_4391918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391918 prefixEnd_4391918 := by exact prefixLift 4391918
  have htrace : WordTrace (prefixWord ++ tailWord_4391918) baseStart_4391918 baseEnd_4391918 := by
    simpa [prefixWord, tailWord_4391918, baseEnd_4391918] using wordTrace_append hprefix tailTrace_4391918
  have hstable : (prefixWord ++ tailWord_4391918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391918).length < 2 ^ (prefixWord ++ tailWord_4391918).sum := by decide
  have hdescent : baseEnd_4391918 < baseStart_4391918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391931 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 7, 2, 2]
def baseStart_4391931 : Nat := 118140960795 + 4391931 * 2 ^ 59
def prefixEnd_4391931 : Nat := 4983230072969 + 3 ^ 40 * 4391931 * 2
def baseEnd_4391931 : Nat := 2255171604381761283464383

theorem tailTrace_4391931 : CollatzResearch.WordTrace tailWord_4391931 prefixEnd_4391931 2255171604381761283464383 := by
  unfold tailWord_4391931
  simp only [CollatzResearch.WordTrace]
  refine ⟨160186883451791543942823647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106791255634527695961882431 160186883451791543942823647)
  ·
    refine ⟨240280325177687315914235471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160186883451791543942823647 240280325177687315914235471)
    ·
      refine ⟨360420487766530973871353207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240280325177687315914235471 360420487766530973871353207)
      ·
        refine ⟨540630731649796460807029811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 360420487766530973871353207 540630731649796460807029811)
        ·
          refine ⟨810946097474694691210544717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 540630731649796460807029811 810946097474694691210544717)
          ·
            refine ⟨304104786553010509203954269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 810946097474694691210544717 304104786553010509203954269)
            ·
              refine ⟨114039294957378940951482851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 304104786553010509203954269 114039294957378940951482851)
              ·
                refine ⟨171058942436068411427224277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114039294957378940951482851 171058942436068411427224277)
                ·
                  refine ⟨4009193963345353392825569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 171058942436068411427224277 4009193963345353392825569)
                  ·
                    refine ⟨3006895472509015044619177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4009193963345353392825569 3006895472509015044619177)
                    ·
                      refine ⟨2255171604381761283464383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3006895472509015044619177 2255171604381761283464383)
                      ·
                        rfl

theorem cell23_4391931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 7, 2, 2].length) (baseStart_4391931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391931 prefixEnd_4391931 := by exact prefixLift 4391931
  have htrace : WordTrace (prefixWord ++ tailWord_4391931) baseStart_4391931 baseEnd_4391931 := by
    simpa [prefixWord, tailWord_4391931, baseEnd_4391931] using wordTrace_append hprefix tailTrace_4391931
  have hstable : (prefixWord ++ tailWord_4391931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391931).length < 2 ^ (prefixWord ++ tailWord_4391931).sum := by decide
  have hdescent : baseEnd_4391931 < baseStart_4391931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391948 : List Nat := [2, 2, 1, 2, 3, 2, 1, 3, 3, 2, 2]
def baseStart_4391948 : Nat := 118140960795 + 4391948 * 2 ^ 59
def prefixEnd_4391948 : Nat := 4983230072969 + 3 ^ 40 * 4391948 * 2
def baseEnd_4391948 : Nat := 2255180333552887716951805

theorem tailTrace_4391948 : CollatzResearch.WordTrace tailWord_4391948 prefixEnd_4391948 2255180333552887716951805 := by
  unfold tailWord_4391948
  simp only [CollatzResearch.WordTrace]
  refine ⟨80093751746364977923096249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106791668995153303897461665 80093751746364977923096249)
  ·
    refine ⟨60070313809773733442322187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80093751746364977923096249 60070313809773733442322187)
    ·
      refine ⟨90105470714660600163483281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60070313809773733442322187 90105470714660600163483281)
      ·
        refine ⟨67579103035995450122612461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90105470714660600163483281 67579103035995450122612461)
        ·
          refine ⟨25342163638498293795979673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67579103035995450122612461 25342163638498293795979673)
          ·
            refine ⟨19006622728873720346984755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25342163638498293795979673 19006622728873720346984755)
            ·
              refine ⟨28509934093310580520477133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19006622728873720346984755 28509934093310580520477133)
              ·
                refine ⟨10691225284991467695178925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28509934093310580520477133 10691225284991467695178925)
                ·
                  refine ⟨4009209481871800385692097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10691225284991467695178925 4009209481871800385692097)
                  ·
                    refine ⟨3006907111403850289269073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4009209481871800385692097 3006907111403850289269073)
                    ·
                      refine ⟨2255180333552887716951805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3006907111403850289269073 2255180333552887716951805)
                      ·
                        rfl

theorem cell23_4391948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 3, 2, 2].length) (baseStart_4391948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391948 prefixEnd_4391948 := by exact prefixLift 4391948
  have htrace : WordTrace (prefixWord ++ tailWord_4391948) baseStart_4391948 baseEnd_4391948 := by
    simpa [prefixWord, tailWord_4391948, baseEnd_4391948] using wordTrace_append hprefix tailTrace_4391948
  have hstable : (prefixWord ++ tailWord_4391948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391948).length < 2 ^ (prefixWord ++ tailWord_4391948).sum := by decide
  have hdescent : baseEnd_4391948 < baseStart_4391948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391971 : List Nat := [1, 1, 1, 4, 3, 4, 2, 7]
def baseStart_4391971 : Nat := 118140960795 + 4391971 * 2 ^ 59
def prefixEnd_4391971 : Nat := 4983230072969 + 3 ^ 40 * 4391971 * 2
def baseEnd_4391971 : Nat := 83525634948442263961637

theorem tailTrace_4391971 : CollatzResearch.WordTrace tailWord_4391971 prefixEnd_4391971 83525634948442263961637 := by
  unfold tailWord_4391971
  simp only [CollatzResearch.WordTrace]
  refine ⟨160188342371646630774279767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106792228247764420516186511 160188342371646630774279767)
  ·
    refine ⟨240282513557469946161419651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160188342371646630774279767 240282513557469946161419651)
    ·
      refine ⟨360423770336204919242129477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240282513557469946161419651 360423770336204919242129477)
      ·
        refine ⟨67579456938038422357899277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 360423770336204919242129477 67579456938038422357899277)
        ·
          refine ⟨25342296351764408384212229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67579456938038422357899277 25342296351764408384212229)
          ·
            refine ⟨4751680565955826572039793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25342296351764408384212229 4751680565955826572039793)
            ·
              refine ⟨3563760424466869929029845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4751680565955826572039793 3563760424466869929029845)
              ·
                refine ⟨83525634948442263961637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3563760424466869929029845 83525634948442263961637)
                ·
                  rfl

theorem cell23_4391971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 7].length) (baseStart_4391971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391971 prefixEnd_4391971 := by exact prefixLift 4391971
  have htrace : WordTrace (prefixWord ++ tailWord_4391971) baseStart_4391971 baseEnd_4391971 := by
    simpa [prefixWord, tailWord_4391971, baseEnd_4391971] using wordTrace_append hprefix tailTrace_4391971
  have hstable : (prefixWord ++ tailWord_4391971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391971).length < 2 ^ (prefixWord ++ tailWord_4391971).sum := by decide
  have hdescent : baseEnd_4391971 < baseStart_4391971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4391991 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 5, 3, 2]
def baseStart_4391991 : Nat := 118140960795 + 4391991 * 2 ^ 59
def prefixEnd_4391991 : Nat := 4983230072969 + 3 ^ 40 * 4391991 * 2
def baseEnd_4391991 : Nat := 2255202413221031048714107

theorem tailTrace_4391991 : CollatzResearch.WordTrace tailWord_4391991 prefixEnd_4391991 2255202413221031048714107 := by
  unfold tailWord_4391991
  simp only [CollatzResearch.WordTrace]
  refine ⟨160189071831574174190007827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106792714554382782793338551 160189071831574174190007827)
  ·
    refine ⟨240283607747361261285011741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160189071831574174190007827 240283607747361261285011741)
    ·
      refine ⟨90106352905260472981879403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 240283607747361261285011741 90106352905260472981879403)
      ·
        refine ⟨135159529357890709472819105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90106352905260472981879403 135159529357890709472819105)
        ·
          refine ⟨101369647018418032104614329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135159529357890709472819105 101369647018418032104614329)
          ·
            refine ⟨76027235263813524078460747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101369647018418032104614329 76027235263813524078460747)
            ·
              refine ⟨114040852895720286117691121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76027235263813524078460747 114040852895720286117691121)
              ·
                refine ⟨85530639671790214588268341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114040852895720286117691121 85530639671790214588268341)
                ·
                  refine ⟨8018497469230332617650157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 85530639671790214588268341 8018497469230332617650157)
                  ·
                    refine ⟨3006936550961374731618809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8018497469230332617650157 3006936550961374731618809)
                    ·
                      refine ⟨2255202413221031048714107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3006936550961374731618809 2255202413221031048714107)
                      ·
                        rfl

theorem cell23_4391991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 3, 2].length) (baseStart_4391991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4391991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4391991 prefixEnd_4391991 := by exact prefixLift 4391991
  have htrace : WordTrace (prefixWord ++ tailWord_4391991) baseStart_4391991 baseEnd_4391991 := by
    simpa [prefixWord, tailWord_4391991, baseEnd_4391991] using wordTrace_append hprefix tailTrace_4391991
  have hstable : (prefixWord ++ tailWord_4391991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4391991).length < 2 ^ (prefixWord ++ tailWord_4391991).sum := by decide
  have hdescent : baseEnd_4391991 < baseStart_4391991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4391991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392014 : List Nat := [4, 1, 1, 1, 1, 3, 2, 1, 1, 8]
def baseStart_4392014 : Nat := 118140960795 + 4392014 * 2 ^ 59
def prefixEnd_4392014 : Nat := 4983230072969 + 3 ^ 40 * 4392014 * 2
def baseEnd_4392014 : Nat := 751738074425361486242167

theorem tailTrace_4392014 : CollatzResearch.WordTrace tailWord_4392014 prefixEnd_4392014 751738074425361486242167 := by
  unfold tailWord_4392014
  simp only [CollatzResearch.WordTrace]
  refine ⟨20023738838811356139761887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106793273806993899412063397 20023738838811356139761887)
  ·
    refine ⟨30035608258217034209642831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20023738838811356139761887 30035608258217034209642831)
    ·
      refine ⟨45053412387325551314464247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30035608258217034209642831 45053412387325551314464247)
      ·
        refine ⟨67580118580988326971696371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45053412387325551314464247 67580118580988326971696371)
        ·
          refine ⟨101370177871482490457544557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67580118580988326971696371 101370177871482490457544557)
          ·
            refine ⟨38013816701805933921579209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101370177871482490457544557 38013816701805933921579209)
            ·
              refine ⟨28510362526354450441184407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38013816701805933921579209 28510362526354450441184407)
              ·
                refine ⟨42765543789531675661776611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28510362526354450441184407 42765543789531675661776611)
                ·
                  refine ⟨64148315684297513492664917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42765543789531675661776611 64148315684297513492664917)
                  ·
                    refine ⟨751738074425361486242167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 64148315684297513492664917 751738074425361486242167)
                    ·
                      rfl

theorem cell23_4392014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_4392014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392014 prefixEnd_4392014 := by exact prefixLift 4392014
  have htrace : WordTrace (prefixWord ++ tailWord_4392014) baseStart_4392014 baseEnd_4392014 := by
    simpa [prefixWord, tailWord_4392014, baseEnd_4392014] using wordTrace_append hprefix tailTrace_4392014
  have hstable : (prefixWord ++ tailWord_4392014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392014).length < 2 ^ (prefixWord ++ tailWord_4392014).sum := by decide
  have hdescent : baseEnd_4392014 < baseStart_4392014 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392024 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 4, 1, 5]
def baseStart_4392024 : Nat := 118140960795 + 4392024 * 2 ^ 59
def prefixEnd_4392024 : Nat := 4983230072969 + 3 ^ 40 * 4392024 * 2
def baseEnd_4392024 : Nat := 2255219358082629419601455

theorem tailTrace_4392024 : CollatzResearch.WordTrace tailWord_4392024 prefixEnd_4392024 2255219358082629419601455 := by
  unfold tailWord_4392024
  simp only [CollatzResearch.WordTrace]
  refine ⟨80095137720227310412979563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106793516960303080550639417 80095137720227310412979563)
  ·
    refine ⟨120142706580340965619469345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80095137720227310412979563 120142706580340965619469345)
    ·
      refine ⟨90107029935255724214602009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120142706580340965619469345 90107029935255724214602009)
      ·
        refine ⟨67580272451441793160951507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90107029935255724214602009 67580272451441793160951507)
        ·
          refine ⟨101370408677162689741427261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67580272451441793160951507 101370408677162689741427261)
          ·
            refine ⟨38013903253936008653035223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101370408677162689741427261 38013903253936008653035223)
            ·
              refine ⟨57020854880904012979552835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38013903253936008653035223 57020854880904012979552835)
              ·
                refine ⟨85531282321356019469329253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57020854880904012979552835 85531282321356019469329253)
                ·
                  refine ⟨16037115435254253650499235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85531282321356019469329253 16037115435254253650499235)
                  ·
                    refine ⟨24055673152881380475748853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16037115435254253650499235 24055673152881380475748853)
                    ·
                      refine ⟨2255219358082629419601455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24055673152881380475748853 2255219358082629419601455)
                      ·
                        rfl

theorem cell23_4392024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_4392024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392024 prefixEnd_4392024 := by exact prefixLift 4392024
  have htrace : WordTrace (prefixWord ++ tailWord_4392024) baseStart_4392024 baseEnd_4392024 := by
    simpa [prefixWord, tailWord_4392024, baseEnd_4392024] using wordTrace_append hprefix tailTrace_4392024
  have hstable : (prefixWord ++ tailWord_4392024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392024).length < 2 ^ (prefixWord ++ tailWord_4392024).sum := by decide
  have hdescent : baseEnd_4392024 < baseStart_4392024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392042 : List Nat := [3, 1, 3, 2, 2, 2, 3, 1, 1, 3, 2]
def baseStart_4392042 : Nat := 118140960795 + 4392042 * 2 ^ 59
def prefixEnd_4392042 : Nat := 4983230072969 + 3 ^ 40 * 4392042 * 2
def baseEnd_4392042 : Nat := 2255228600734410349176373

theorem tailTrace_4392042 : CollatzResearch.WordTrace tailWord_4392042 prefixEnd_4392042 2255228600734410349176373 := by
  unfold tailWord_4392042
  simp only [CollatzResearch.WordTrace]
  refine ⟨40047732988597352475028595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106793954636259606600076253 40047732988597352475028595)
  ·
    refine ⟨60071599482896028712542893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40047732988597352475028595 60071599482896028712542893)
    ·
      refine ⟨22526849806086010767203585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60071599482896028712542893 22526849806086010767203585)
      ·
        refine ⟨16895137354564508075402689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22526849806086010767203585 16895137354564508075402689)
        ·
          refine ⟨12671353015923381056552017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16895137354564508075402689 12671353015923381056552017)
          ·
            refine ⟨9503514761942535792414013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12671353015923381056552017 9503514761942535792414013)
            ·
              refine ⟨3563818035728450922155255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9503514761942535792414013 3563818035728450922155255)
              ·
                refine ⟨5345727053592676383232883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3563818035728450922155255 5345727053592676383232883)
                ·
                  refine ⟨8018590580389014574849325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5345727053592676383232883 8018590580389014574849325)
                  ·
                    refine ⟨3006971467645880465568497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8018590580389014574849325 3006971467645880465568497)
                    ·
                      refine ⟨2255228600734410349176373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3006971467645880465568497 2255228600734410349176373)
                      ·
                        rfl

theorem cell23_4392042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_4392042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392042 prefixEnd_4392042 := by exact prefixLift 4392042
  have htrace : WordTrace (prefixWord ++ tailWord_4392042) baseStart_4392042 baseEnd_4392042 := by
    simpa [prefixWord, tailWord_4392042, baseEnd_4392042] using wordTrace_append hprefix tailTrace_4392042
  have hstable : (prefixWord ++ tailWord_4392042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392042).length < 2 ^ (prefixWord ++ tailWord_4392042).sum := by decide
  have hdescent : baseEnd_4392042 < baseStart_4392042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392055 : List Nat := [1, 1, 3, 1, 1, 4, 4, 2, 2, 2, 2]
def baseStart_4392055 : Nat := 118140960795 + 4392055 * 2 ^ 59
def prefixEnd_4392055 : Nat := 4983230072969 + 3 ^ 40 * 4392055 * 2
def baseEnd_4392055 : Nat := 2255235275982918798313813

theorem tailTrace_4392055 : CollatzResearch.WordTrace tailWord_4392055 prefixEnd_4392055 2255235275982918798313813 := by
  unfold tailWord_4392055
  simp only [CollatzResearch.WordTrace]
  refine ⟨160191406103342313120337619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106794270735561542080225079 160191406103342313120337619)
  ·
    refine ⟨240287109155013469680506429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160191406103342313120337619 240287109155013469680506429)
    ·
      refine ⟨90107665933130051130189911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 240287109155013469680506429 90107665933130051130189911)
      ·
        refine ⟨135161498899695076695284867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90107665933130051130189911 135161498899695076695284867)
        ·
          refine ⟨202742248349542615042927301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135161498899695076695284867 202742248349542615042927301)
          ·
            refine ⟨38014171565539240320548869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 202742248349542615042927301 38014171565539240320548869)
            ·
              refine ⟨7127657168538607560102913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38014171565539240320548869 7127657168538607560102913)
              ·
                refine ⟨5345742876403955670077185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7127657168538607560102913 5345742876403955670077185)
                ·
                  refine ⟨4009307157302966752557889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5345742876403955670077185 4009307157302966752557889)
                  ·
                    refine ⟨3006980367977225064418417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4009307157302966752557889 3006980367977225064418417)
                    ·
                      refine ⟨2255235275982918798313813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3006980367977225064418417 2255235275982918798313813)
                      ·
                        rfl

theorem cell23_4392055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 2, 2, 2, 2].length) (baseStart_4392055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392055 prefixEnd_4392055 := by exact prefixLift 4392055
  have htrace : WordTrace (prefixWord ++ tailWord_4392055) baseStart_4392055 baseEnd_4392055 := by
    simpa [prefixWord, tailWord_4392055, baseEnd_4392055] using wordTrace_append hprefix tailTrace_4392055
  have hstable : (prefixWord ++ tailWord_4392055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392055).length < 2 ^ (prefixWord ++ tailWord_4392055).sum := by decide
  have hdescent : baseEnd_4392055 < baseStart_4392055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392095 : List Nat := [1, 1, 2, 6, 2, 1, 2, 3, 5]
def baseStart_4392095 : Nat := 118140960795 + 4392095 * 2 ^ 59
def prefixEnd_4392095 : Nat := 4983230072969 + 3 ^ 40 * 4392095 * 2
def baseEnd_4392095 : Nat := 250583979467677626868181

theorem tailTrace_4392095 : CollatzResearch.WordTrace tailWord_4392095 prefixEnd_4392095 250583979467677626868181 := by
  unfold tailWord_4392095
  simp only [CollatzResearch.WordTrace]
  refine ⟨160192865023197399951793739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106795243348798266634529159 160192865023197399951793739)
  ·
    refine ⟨240289297534796099927690609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160192865023197399951793739 240289297534796099927690609)
    ·
      refine ⟨180216973151097074945767957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240289297534796099927690609 180216973151097074945767957)
      ·
        refine ⟨8447670616457675388082873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 180216973151097074945767957 8447670616457675388082873)
        ·
          refine ⟨6335752962343256541062155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8447670616457675388082873 6335752962343256541062155)
          ·
            refine ⟨9503629443514884811593233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6335752962343256541062155 9503629443514884811593233)
            ·
              refine ⟨7127722082636163608694925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9503629443514884811593233 7127722082636163608694925)
              ·
                refine ⟨2672895780988561353260597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7127722082636163608694925 2672895780988561353260597)
                ·
                  refine ⟨250583979467677626868181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2672895780988561353260597 250583979467677626868181)
                  ·
                    rfl

theorem cell23_4392095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 3, 5].length) (baseStart_4392095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392095 prefixEnd_4392095 := by exact prefixLift 4392095
  have htrace : WordTrace (prefixWord ++ tailWord_4392095) baseStart_4392095 baseEnd_4392095 := by
    simpa [prefixWord, tailWord_4392095, baseEnd_4392095] using wordTrace_append hprefix tailTrace_4392095
  have hstable : (prefixWord ++ tailWord_4392095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392095).length < 2 ^ (prefixWord ++ tailWord_4392095).sum := by decide
  have hdescent : baseEnd_4392095 < baseStart_4392095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392111 : List Nat := [1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 4]
def baseStart_4392111 : Nat := 118140960795 + 4392111 * 2 ^ 59
def prefixEnd_4392111 : Nat := 4983230072969 + 3 ^ 40 * 4392111 * 2
def baseEnd_4392111 : Nat := 2255264030899570579213555

theorem tailTrace_4392111 : CollatzResearch.WordTrace tailWord_4392111 prefixEnd_4392111 2255264030899570579213555 := by
  unfold tailWord_4392111
  simp only [CollatzResearch.WordTrace]
  refine ⟨160193448591139434684376187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106795632394092956456250791 160193448591139434684376187)
  ·
    refine ⟨240290172886709152026564281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160193448591139434684376187 240290172886709152026564281)
    ·
      refine ⟨180217629665031864019923211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240290172886709152026564281 180217629665031864019923211)
      ·
        refine ⟨270326444497547796029884817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180217629665031864019923211 270326444497547796029884817)
        ·
          refine ⟨202744833373160847022413613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 270326444497547796029884817 202744833373160847022413613)
          ·
            refine ⟨76029312514935317633405105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 202744833373160847022413613 76029312514935317633405105)
            ·
              refine ⟨57021984386201488225053829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76029312514935317633405105 57021984386201488225053829)
              ·
                refine ⟨10691622072412779042197593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57021984386201488225053829 10691622072412779042197593)
                ·
                  refine ⟨8018716554309584281648195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10691622072412779042197593 8018716554309584281648195)
                  ·
                    refine ⟨12028074831464376422472293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8018716554309584281648195 12028074831464376422472293)
                    ·
                      refine ⟨2255264030899570579213555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12028074831464376422472293 2255264030899570579213555)
                      ·
                        rfl

theorem cell23_4392111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 4].length) (baseStart_4392111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392111 prefixEnd_4392111 := by exact prefixLift 4392111
  have htrace : WordTrace (prefixWord ++ tailWord_4392111) baseStart_4392111 baseEnd_4392111 := by
    simpa [prefixWord, tailWord_4392111, baseEnd_4392111] using wordTrace_append hprefix tailTrace_4392111
  have hstable : (prefixWord ++ tailWord_4392111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392111).length < 2 ^ (prefixWord ++ tailWord_4392111).sum := by decide
  have hdescent : baseEnd_4392111 < baseStart_4392111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392131 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 6, 2, 3]
def baseStart_4392131 : Nat := 118140960795 + 4392131 * 2 ^ 59
def prefixEnd_4392131 : Nat := 4983230072969 + 3 ^ 40 * 4392131 * 2
def baseEnd_4392131 : Nat := 2255274300512660500963463

theorem tailTrace_4392131 : CollatzResearch.WordTrace tailWord_4392131 prefixEnd_4392131 2255274300512660500963463 := by
  unfold tailWord_4392131
  simp only [CollatzResearch.WordTrace]
  refine ⟨160194178051066978100104247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106796118700711318733402831 160194178051066978100104247)
  ·
    refine ⟨240291267076600467150156371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160194178051066978100104247 240291267076600467150156371)
    ·
      refine ⟨360436900614900700725234557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240291267076600467150156371 360436900614900700725234557)
      ·
        refine ⟨135163837730587762771962959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 360436900614900700725234557 135163837730587762771962959)
        ·
          refine ⟨202745756595881644157944439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135163837730587762771962959 202745756595881644157944439)
          ·
            refine ⟨304118634893822466236916659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202745756595881644157944439 304118634893822466236916659)
            ·
              refine ⟨456177952340733699355374989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304118634893822466236916659 456177952340733699355374989)
              ·
                refine ⟨171066732127775137258265621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 456177952340733699355374989 171066732127775137258265621)
                ·
                  refine ⟨8018753068489459558981201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 171066732127775137258265621 8018753068489459558981201)
                  ·
                    refine ⟨6014064801367094669235901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8018753068489459558981201 6014064801367094669235901)
                    ·
                      refine ⟨2255274300512660500963463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6014064801367094669235901 2255274300512660500963463)
                      ·
                        rfl

theorem cell23_4392131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 6, 2, 3].length) (baseStart_4392131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392131 prefixEnd_4392131 := by exact prefixLift 4392131
  have htrace : WordTrace (prefixWord ++ tailWord_4392131) baseStart_4392131 baseEnd_4392131 := by
    simpa [prefixWord, tailWord_4392131, baseEnd_4392131] using wordTrace_append hprefix tailTrace_4392131
  have hstable : (prefixWord ++ tailWord_4392131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392131).length < 2 ^ (prefixWord ++ tailWord_4392131).sum := by decide
  have hdescent : baseEnd_4392131 < baseStart_4392131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392138 : List Nat := [3, 1, 2, 1, 3, 2, 2, 2, 3, 4]
def baseStart_4392138 : Nat := 118140960795 + 4392138 * 2 ^ 59
def prefixEnd_4392138 : Nat := 4983230072969 + 3 ^ 40 * 4392138 * 2
def baseEnd_4392138 : Nat := 751759298292413991191977

theorem tailTrace_4392138 : CollatzResearch.WordTrace tailWord_4392138 prefixEnd_4392138 751759298292413991191977 := by
  unfold tailWord_4392138
  simp only [CollatzResearch.WordTrace]
  refine ⟨40048608340510404573902267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106796288908027745530406045 40048608340510404573902267)
  ·
    refine ⟨60072912510765606860853401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40048608340510404573902267 60072912510765606860853401)
    ·
      refine ⟨45054684383074205145640051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60072912510765606860853401 45054684383074205145640051)
      ·
        refine ⟨67582026574611307718460077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45054684383074205145640051 67582026574611307718460077)
        ·
          refine ⟨25343259965479240394422529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67582026574611307718460077 25343259965479240394422529)
          ·
            refine ⟨19007444974109430295816897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25343259965479240394422529 19007444974109430295816897)
            ·
              refine ⟨14255583730582072721862673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19007444974109430295816897 14255583730582072721862673)
              ·
                refine ⟨10691687797936554541397005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14255583730582072721862673 10691687797936554541397005)
                ·
                  refine ⟨4009382924226207953023877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10691687797936554541397005 4009382924226207953023877)
                  ·
                    refine ⟨751759298292413991191977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4009382924226207953023877 751759298292413991191977)
                    ·
                      rfl

theorem cell23_4392138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 3, 4].length) (baseStart_4392138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392138 prefixEnd_4392138 := by exact prefixLift 4392138
  have htrace : WordTrace (prefixWord ++ tailWord_4392138) baseStart_4392138 baseEnd_4392138 := by
    simpa [prefixWord, tailWord_4392138, baseEnd_4392138] using wordTrace_append hprefix tailTrace_4392138
  have hstable : (prefixWord ++ tailWord_4392138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392138).length < 2 ^ (prefixWord ++ tailWord_4392138).sum := by decide
  have hdescent : baseEnd_4392138 < baseStart_4392138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392144 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 9]
def baseStart_4392144 : Nat := 118140960795 + 4392144 * 2 ^ 59
def prefixEnd_4392144 : Nat := 4983230072969 + 3 ^ 40 * 4392144 * 2
def baseEnd_4392144 : Nat := 2255280975761168950100903

theorem tailTrace_4392144 : CollatzResearch.WordTrace tailWord_4392144 prefixEnd_4392144 2255280975761168950100903 := by
  unfold tailWord_4392144
  simp only [CollatzResearch.WordTrace]
  refine ⟨80097326100009940660163743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106796434800013254213551657 80097326100009940660163743)
  ·
    refine ⟨120145989150014910990245615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80097326100009940660163743 120145989150014910990245615)
    ·
      refine ⟨180218983725022366485368423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120145989150014910990245615 180218983725022366485368423)
      ·
        refine ⟨270328475587533549728052635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180218983725022366485368423 270328475587533549728052635)
        ·
          refine ⟨405492713381300324592078953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270328475587533549728052635 405492713381300324592078953)
          ·
            refine ⟨304119535035975243444059215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 405492713381300324592078953 304119535035975243444059215)
            ·
              refine ⟨456179302553962865166088823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304119535035975243444059215 456179302553962865166088823)
              ·
                refine ⟨684268953830944297749133235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 456179302553962865166088823 684268953830944297749133235)
                ·
                  refine ⟨1026403430746416446623699853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 684268953830944297749133235 1026403430746416446623699853)
                  ·
                    refine ⟨384901286529906167483887445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1026403430746416446623699853 384901286529906167483887445)
                    ·
                      refine ⟨2255280975761168950100903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 384901286529906167483887445 2255280975761168950100903)
                      ·
                        rfl

theorem cell23_4392144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 9].length) (baseStart_4392144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392144 prefixEnd_4392144 := by exact prefixLift 4392144
  have htrace : WordTrace (prefixWord ++ tailWord_4392144) baseStart_4392144 baseEnd_4392144 := by
    simpa [prefixWord, tailWord_4392144, baseEnd_4392144] using wordTrace_append hprefix tailTrace_4392144
  have hstable : (prefixWord ++ tailWord_4392144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392144).length < 2 ^ (prefixWord ++ tailWord_4392144).sum := by decide
  have hdescent : baseEnd_4392144 < baseStart_4392144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392165 : List Nat := [1, 3, 1, 4, 3, 1, 1, 2, 2, 2, 3]
def baseStart_4392165 : Nat := 118140960795 + 4392165 * 2 ^ 59
def prefixEnd_4392165 : Nat := 4983230072969 + 3 ^ 40 * 4392165 * 2
def baseEnd_4392165 : Nat := 2255291758854913367938307

theorem tailTrace_4392165 : CollatzResearch.WordTrace tailWord_4392165 prefixEnd_4392165 2255291758854913367938307 := by
  unfold tailWord_4392165
  simp only [CollatzResearch.WordTrace]
  refine ⟨160195418132943801906841949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106796945421962534604561299 160195418132943801906841949)
  ·
    refine ⟨60073281799853925715065731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160195418132943801906841949 60073281799853925715065731)
    ·
      refine ⟨90109922699780888572598597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60073281799853925715065731 90109922699780888572598597)
      ·
        refine ⟨16895610506208916607362237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90109922699780888572598597 16895610506208916607362237)
        ·
          refine ⟨6335853939828343727760839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16895610506208916607362237 6335853939828343727760839)
          ·
            refine ⟨9503780909742515591641259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6335853939828343727760839 9503780909742515591641259)
            ·
              refine ⟨14255671364613773387461889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9503780909742515591641259 14255671364613773387461889)
              ·
                refine ⟨10691753523460330040596417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14255671364613773387461889 10691753523460330040596417)
                ·
                  refine ⟨8018815142595247530447313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10691753523460330040596417 8018815142595247530447313)
                  ·
                    refine ⟨6014111356946435647835485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8018815142595247530447313 6014111356946435647835485)
                    ·
                      refine ⟨2255291758854913367938307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6014111356946435647835485 2255291758854913367938307)
                      ·
                        rfl

theorem cell23_4392165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_4392165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392165 prefixEnd_4392165 := by exact prefixLift 4392165
  have htrace : WordTrace (prefixWord ++ tailWord_4392165) baseStart_4392165 baseEnd_4392165 := by
    simpa [prefixWord, tailWord_4392165, baseEnd_4392165] using wordTrace_append hprefix tailTrace_4392165
  have hstable : (prefixWord ++ tailWord_4392165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392165).length < 2 ^ (prefixWord ++ tailWord_4392165).sum := by decide
  have hdescent : baseEnd_4392165 < baseStart_4392165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392172 : List Nat := [2, 2, 1, 1, 2, 5, 3, 2, 1, 4]
def baseStart_4392172 : Nat := 118140960795 + 4392172 * 2 ^ 59
def prefixEnd_4392172 : Nat := 4983230072969 + 3 ^ 40 * 4392172 * 2
def baseEnd_4392172 : Nat := 751765117739831613516925

theorem tailTrace_4392172 : CollatzResearch.WordTrace tailWord_4392172 prefixEnd_4392172 751765117739831613516925 := by
  unfold tailWord_4392172
  simp only [CollatzResearch.WordTrace]
  refine ⟨80097836721959221051173385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106797115629278961401564513 80097836721959221051173385)
  ·
    refine ⟨60073377541469415788380039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80097836721959221051173385 60073377541469415788380039)
    ·
      refine ⟨90110066312204123682570059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60073377541469415788380039 90110066312204123682570059)
      ·
        refine ⟨135165099468306185523855089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90110066312204123682570059 135165099468306185523855089)
        ·
          refine ⟨101373824601229639142891317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135165099468306185523855089 101373824601229639142891317)
          ·
            refine ⟨9503796056365278669646061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 101373824601229639142891317 9503796056365278669646061)
            ·
              refine ⟨3563923521136979501117273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9503796056365278669646061 3563923521136979501117273)
              ·
                refine ⟨2672942640852734625837955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3563923521136979501117273 2672942640852734625837955)
                ·
                  refine ⟨4009413961279101938756933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2672942640852734625837955 4009413961279101938756933)
                  ·
                    refine ⟨751765117739831613516925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4009413961279101938756933 751765117739831613516925)
                    ·
                      rfl

theorem cell23_4392172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 2, 1, 4].length) (baseStart_4392172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392172 prefixEnd_4392172 := by exact prefixLift 4392172
  have htrace : WordTrace (prefixWord ++ tailWord_4392172) baseStart_4392172 baseEnd_4392172 := by
    simpa [prefixWord, tailWord_4392172, baseEnd_4392172] using wordTrace_append hprefix tailTrace_4392172
  have hstable : (prefixWord ++ tailWord_4392172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392172).length < 2 ^ (prefixWord ++ tailWord_4392172).sum := by decide
  have hdescent : baseEnd_4392172 < baseStart_4392172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392215 : List Nat := [1, 1, 3, 4, 1, 1, 5, 1, 1, 5]
def baseStart_4392215 : Nat := 118140960795 + 4392215 * 2 ^ 59
def prefixEnd_4392215 : Nat := 4983230072969 + 3 ^ 40 * 4392215 * 2
def baseEnd_4392215 : Nat := 751772477629212724104359

theorem tailTrace_4392215 : CollatzResearch.WordTrace tailWord_4392215 prefixEnd_4392215 751772477629212724104359 := by
  unfold tailWord_4392215
  simp only [CollatzResearch.WordTrace]
  refine ⟨160197241782762660446162099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106798161188508440297441399 160197241782762660446162099)
  ·
    refine ⟨240295862674143990669243149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160197241782762660446162099 240295862674143990669243149)
    ·
      refine ⟨90110948502803996500966181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 240295862674143990669243149 90110948502803996500966181)
      ·
        refine ⟨16895802844275749343931159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90110948502803996500966181 16895802844275749343931159)
        ·
          refine ⟨25343704266413624015896739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16895802844275749343931159 25343704266413624015896739)
          ·
            refine ⟨38015556399620436023845109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25343704266413624015896739 38015556399620436023845109)
            ·
              refine ⟨3563958412464415877235479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38015556399620436023845109 3563958412464415877235479)
              ·
                refine ⟨5345937618696623815853219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3563958412464415877235479 5345937618696623815853219)
                ·
                  refine ⟨8018906428044935723779829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5345937618696623815853219 8018906428044935723779829)
                  ·
                    refine ⟨751772477629212724104359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8018906428044935723779829 751772477629212724104359)
                    ·
                      rfl

theorem cell23_4392215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 1, 5].length) (baseStart_4392215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392215 prefixEnd_4392215 := by exact prefixLift 4392215
  have htrace : WordTrace (prefixWord ++ tailWord_4392215) baseStart_4392215 baseEnd_4392215 := by
    simpa [prefixWord, tailWord_4392215, baseEnd_4392215] using wordTrace_append hprefix tailTrace_4392215
  have hstable : (prefixWord ++ tailWord_4392215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392215).length < 2 ^ (prefixWord ++ tailWord_4392215).sum := by decide
  have hdescent : baseEnd_4392215 < baseStart_4392215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392229 : List Nat := [1, 3, 1, 2, 4, 1, 4, 2, 1, 1, 3]
def baseStart_4392229 : Nat := 118140960795 + 4392229 * 2 ^ 59
def prefixEnd_4392229 : Nat := 4983230072969 + 3 ^ 40 * 4392229 * 2
def baseEnd_4392229 : Nat := 2255324621616801117538013

theorem tailTrace_4392229 : CollatzResearch.WordTrace tailWord_4392229 prefixEnd_4392229 2255324621616801117538013 := by
  unfold tailWord_4392229
  simp only [CollatzResearch.WordTrace]
  refine ⟨160197752404711940837171741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106798501603141293891447827 160197752404711940837171741)
  ·
    refine ⟨60074157151766977813939403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160197752404711940837171741 60074157151766977813939403)
    ·
      refine ⟨90111235727650466720909105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60074157151766977813939403 90111235727650466720909105)
      ·
        refine ⟨67583426795737850040681829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90111235727650466720909105 67583426795737850040681829)
        ·
          refine ⟨12671892524200846882627843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67583426795737850040681829 12671892524200846882627843)
          ·
            refine ⟨19007838786301270323941765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12671892524200846882627843 19007838786301270323941765)
            ·
              refine ⟨3563969772431488185739081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19007838786301270323941765 3563969772431488185739081)
              ·
                refine ⟨2672977329323616139304311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3563969772431488185739081 2672977329323616139304311)
                ·
                  refine ⟨4009465993985424208956467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2672977329323616139304311 4009465993985424208956467)
                  ·
                    refine ⟨6014198990978136313434701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4009465993985424208956467 6014198990978136313434701)
                    ·
                      refine ⟨2255324621616801117538013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6014198990978136313434701 2255324621616801117538013)
                      ·
                        rfl

theorem cell23_4392229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 2, 1, 1, 3].length) (baseStart_4392229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392229 prefixEnd_4392229 := by exact prefixLift 4392229
  have htrace : WordTrace (prefixWord ++ tailWord_4392229) baseStart_4392229 baseEnd_4392229 := by
    simpa [prefixWord, tailWord_4392229, baseEnd_4392229] using wordTrace_append hprefix tailTrace_4392229
  have hstable : (prefixWord ++ tailWord_4392229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392229).length < 2 ^ (prefixWord ++ tailWord_4392229).sum := by decide
  have hdescent : baseEnd_4392229 < baseStart_4392229 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392245 : List Nat := [1, 3, 3, 1, 2, 2, 2, 3, 2, 4]
def baseStart_4392245 : Nat := 118140960795 + 4392245 * 2 ^ 59
def prefixEnd_4392245 : Nat := 4983230072969 + 3 ^ 40 * 4392245 * 2
def baseEnd_4392245 : Nat := 751777612435757684979313

theorem tailTrace_4392245 : CollatzResearch.WordTrace tailWord_4392245 prefixEnd_4392245 751777612435757684979313 := by
  unfold tailWord_4392245
  simp only [CollatzResearch.WordTrace]
  refine ⟨160198335972653975569754189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106798890648435983713169459 160198335972653975569754189)
  ·
    refine ⟨60074375989745240838657821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160198335972653975569754189 60074375989745240838657821)
    ·
      refine ⟨22527890996154465314496683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60074375989745240838657821 22527890996154465314496683)
      ·
        refine ⟨33791836494231697971745025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22527890996154465314496683 33791836494231697971745025)
        ·
          refine ⟨25343877370673773478808769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33791836494231697971745025 25343877370673773478808769)
          ·
            refine ⟨19007908028005330109106577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25343877370673773478808769 19007908028005330109106577)
            ·
              refine ⟨14255931021003997581829933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19007908028005330109106577 14255931021003997581829933)
              ·
                refine ⟨5345974132876499093186225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14255931021003997581829933 5345974132876499093186225)
                ·
                  refine ⟨4009480599657374319889669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5345974132876499093186225 4009480599657374319889669)
                  ·
                    refine ⟨751777612435757684979313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4009480599657374319889669 751777612435757684979313)
                    ·
                      rfl

theorem cell23_4392245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_4392245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392245 prefixEnd_4392245 := by exact prefixLift 4392245
  have htrace : WordTrace (prefixWord ++ tailWord_4392245) baseStart_4392245 baseEnd_4392245 := by
    simpa [prefixWord, tailWord_4392245, baseEnd_4392245] using wordTrace_append hprefix tailTrace_4392245
  have hstable : (prefixWord ++ tailWord_4392245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392245).length < 2 ^ (prefixWord ++ tailWord_4392245).sum := by decide
  have hdescent : baseEnd_4392245 < baseStart_4392245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392252 : List Nat := [2, 2, 2, 2, 1, 4, 1, 2, 3, 2, 2]
def baseStart_4392252 : Nat := 118140960795 + 4392252 * 2 ^ 59
def prefixEnd_4392252 : Nat := 4983230072969 + 3 ^ 40 * 4392252 * 2
def baseEnd_4392252 : Nat := 2255336431671854527550407

theorem tailTrace_4392252 : CollatzResearch.WordTrace tailWord_4392252 prefixEnd_4392252 2255336431671854527550407 := by
  unfold tailWord_4392252
  simp only [CollatzResearch.WordTrace]
  refine ⟨80099295641814307882629505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106799060855752410510172673 80099295641814307882629505)
  ·
    refine ⟨60074471731360730911972129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80099295641814307882629505 60074471731360730911972129)
    ·
      refine ⟨45055853798520548183979097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60074471731360730911972129 45055853798520548183979097)
      ·
        refine ⟨33791890348890411137984323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45055853798520548183979097 33791890348890411137984323)
        ·
          refine ⟨50687835523335616706976485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33791890348890411137984323 50687835523335616706976485)
          ·
            refine ⟨9503969160625428132558091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50687835523335616706976485 9503969160625428132558091)
            ·
              refine ⟨14255953740938142198837137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9503969160625428132558091 14255953740938142198837137)
              ·
                refine ⟨10691965305703606649127853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14255953740938142198837137 10691965305703606649127853)
                ·
                  refine ⟨4009486989638852493422945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10691965305703606649127853 4009486989638852493422945)
                  ·
                    refine ⟨3007115242229139370067209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4009486989638852493422945 3007115242229139370067209)
                    ·
                      refine ⟨2255336431671854527550407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3007115242229139370067209 2255336431671854527550407)
                      ·
                        rfl

theorem cell23_4392252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_4392252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392252 prefixEnd_4392252 := by exact prefixLift 4392252
  have htrace : WordTrace (prefixWord ++ tailWord_4392252) baseStart_4392252 baseEnd_4392252 := by
    simpa [prefixWord, tailWord_4392252, baseEnd_4392252] using wordTrace_append hprefix tailTrace_4392252
  have hstable : (prefixWord ++ tailWord_4392252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392252).length < 2 ^ (prefixWord ++ tailWord_4392252).sum := by decide
  have hdescent : baseEnd_4392252 < baseStart_4392252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392269 : List Nat := [1, 6, 1, 3, 1, 1, 1, 3, 1, 1, 4]
def baseStart_4392269 : Nat := 118140960795 + 4392269 * 2 ^ 59
def prefixEnd_4392269 : Nat := 4983230072969 + 3 ^ 40 * 4392269 * 2
def baseEnd_4392269 : Nat := 2255345160842980961037829

theorem tailTrace_4392269 : CollatzResearch.WordTrace tailWord_4392269 prefixEnd_4392269 2255345160842980961037829 := by
  unfold tailWord_4392269
  simp only [CollatzResearch.WordTrace]
  refine ⟨160199211324567027668627861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106799474216378018445751907 160199211324567027668627861)
  ·
    refine ⟨7509338030839079421966931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 160199211324567027668627861 7509338030839079421966931)
    ·
      refine ⟨11264007046258619132950397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7509338030839079421966931 11264007046258619132950397)
      ·
        refine ⟨4224002642346982174856399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11264007046258619132950397 4224002642346982174856399)
        ·
          refine ⟨6336003963520473262284599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4224002642346982174856399 6336003963520473262284599)
          ·
            refine ⟨9504005945280709893426899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6336003963520473262284599 9504005945280709893426899)
            ·
              refine ⟨14256008917921064840140349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9504005945280709893426899 14256008917921064840140349)
              ·
                refine ⟨5346003344220399315052631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14256008917921064840140349 5346003344220399315052631)
                ·
                  refine ⟨8019005016330598972578947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5346003344220399315052631 8019005016330598972578947)
                  ·
                    refine ⟨12028507524495898458868421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8019005016330598972578947 12028507524495898458868421)
                    ·
                      refine ⟨2255345160842980961037829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12028507524495898458868421 2255345160842980961037829)
                      ·
                        rfl

theorem cell23_4392269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_4392269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392269 prefixEnd_4392269 := by exact prefixLift 4392269
  have htrace : WordTrace (prefixWord ++ tailWord_4392269) baseStart_4392269 baseEnd_4392269 := by
    simpa [prefixWord, tailWord_4392269, baseEnd_4392269] using wordTrace_append hprefix tailTrace_4392269
  have hstable : (prefixWord ++ tailWord_4392269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392269).length < 2 ^ (prefixWord ++ tailWord_4392269).sum := by decide
  have hdescent : baseEnd_4392269 < baseStart_4392269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392325 : List Nat := [1, 3, 1, 1, 3, 1, 2, 4, 1, 4, 2]
def baseStart_4392325 : Nat := 118140960795 + 4392325 * 2 ^ 59
def prefixEnd_4392325 : Nat := 4983230072969 + 3 ^ 40 * 4392325 * 2
def baseEnd_4392325 : Nat := 2255373915759632741937571

theorem tailTrace_4392325 : CollatzResearch.WordTrace tailWord_4392325 prefixEnd_4392325 2255373915759632741937571 := by
  unfold tailWord_4392325
  simp only [CollatzResearch.WordTrace]
  refine ⟨160201253812364149232666429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106800835874909432821777619 160201253812364149232666429)
  ·
    refine ⟨60075470179636555962249911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160201253812364149232666429 60075470179636555962249911)
    ·
      refine ⟨90113205269454833943374867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60075470179636555962249911 90113205269454833943374867)
      ·
        refine ⟨135169807904182250915062301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90113205269454833943374867 135169807904182250915062301)
        ·
          refine ⟨50688677964068344093148363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135169807904182250915062301 50688677964068344093148363)
          ·
            refine ⟨76033016946102516139722545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50688677964068344093148363 76033016946102516139722545)
            ·
              refine ⟨57024762709576887104791909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76033016946102516139722545 57024762709576887104791909)
              ·
                refine ⟨10692143008045666332148483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57024762709576887104791909 10692143008045666332148483)
                ·
                  refine ⟨16038214512068499498222725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10692143008045666332148483 16038214512068499498222725)
                  ·
                    refine ⟨3007165221012843655916761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16038214512068499498222725 3007165221012843655916761)
                    ·
                      refine ⟨2255373915759632741937571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3007165221012843655916761 2255373915759632741937571)
                      ·
                        rfl

theorem cell23_4392325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 4, 2].length) (baseStart_4392325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392325 prefixEnd_4392325 := by exact prefixLift 4392325
  have htrace : WordTrace (prefixWord ++ tailWord_4392325) baseStart_4392325 baseEnd_4392325 := by
    simpa [prefixWord, tailWord_4392325, baseEnd_4392325] using wordTrace_append hprefix tailTrace_4392325
  have hstable : (prefixWord ++ tailWord_4392325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392325).length < 2 ^ (prefixWord ++ tailWord_4392325).sum := by decide
  have hdescent : baseEnd_4392325 < baseStart_4392325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392328 : List Nat := [2, 1, 3, 3, 1, 2, 1, 1, 1, 3, 5]
def baseStart_4392328 : Nat := 118140960795 + 4392328 * 2 ^ 59
def prefixEnd_4392328 : Nat := 4983230072969 + 3 ^ 40 * 4392328 * 2
def baseEnd_4392328 : Nat := 2255375456201596230200057

theorem tailTrace_4392328 : CollatzResearch.WordTrace tailWord_4392328 prefixEnd_4392328 2255375456201596230200057 := by
  unfold tailWord_4392328
  simp only [CollatzResearch.WordTrace]
  refine ⟨80100681615676640372512819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106800908820902187163350425 80100681615676640372512819)
  ·
    refine ⟨120151022423514960558769229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80100681615676640372512819 120151022423514960558769229)
    ·
      refine ⟨45056633408818110209538461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120151022423514960558769229 45056633408818110209538461)
      ·
        refine ⟨16896237528306791328576923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45056633408818110209538461 16896237528306791328576923)
        ·
          refine ⟨25344356292460186992865385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16896237528306791328576923 25344356292460186992865385)
          ·
            refine ⟨19008267219345140244649039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25344356292460186992865385 19008267219345140244649039)
            ·
              refine ⟨28512400829017710366973559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19008267219345140244649039 28512400829017710366973559)
              ·
                refine ⟨42768601243526565550460339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28512400829017710366973559 42768601243526565550460339)
                ·
                  refine ⟨64152901865289848325690509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42768601243526565550460339 64152901865289848325690509)
                  ·
                    refine ⟨24057338199483693122133941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64152901865289848325690509 24057338199483693122133941)
                    ·
                      refine ⟨2255375456201596230200057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24057338199483693122133941 2255375456201596230200057)
                      ·
                        rfl

theorem cell23_4392328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_4392328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392328 prefixEnd_4392328 := by exact prefixLift 4392328
  have htrace : WordTrace (prefixWord ++ tailWord_4392328) baseStart_4392328 baseEnd_4392328 := by
    simpa [prefixWord, tailWord_4392328, baseEnd_4392328] using wordTrace_append hprefix tailTrace_4392328
  have hstable : (prefixWord ++ tailWord_4392328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392328).length < 2 ^ (prefixWord ++ tailWord_4392328).sum := by decide
  have hdescent : baseEnd_4392328 < baseStart_4392328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392359 : List Nat := [1, 1, 6, 1, 1, 1, 3, 3, 2, 2, 2]
def baseStart_4392359 : Nat := 118140960795 + 4392359 * 2 ^ 59
def prefixEnd_4392359 : Nat := 4983230072969 + 3 ^ 40 * 4392359 * 2
def baseEnd_4392359 : Nat := 2255391374101885608912415

theorem tailTrace_4392359 : CollatzResearch.WordTrace tailWord_4392359 prefixEnd_4392359 2255391374101885608912415 := by
  unfold tailWord_4392359
  simp only [CollatzResearch.WordTrace]
  refine ⟨160202493894240973039404131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106801662596160648692936087 160202493894240973039404131)
  ·
    refine ⟨240303740841361459559106197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160202493894240973039404131 240303740841361459559106197)
    ·
      refine ⟨11264237851938818416833103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 240303740841361459559106197 11264237851938818416833103)
      ·
        refine ⟨16896356777908227625249655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11264237851938818416833103 16896356777908227625249655)
        ·
          refine ⟨25344535166862341437874483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16896356777908227625249655 25344535166862341437874483)
          ·
            refine ⟨38016802750293512156811725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25344535166862341437874483 38016802750293512156811725)
            ·
              refine ⟨14256301031360067058804397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38016802750293512156811725 14256301031360067058804397)
              ·
                refine ⟨5346112886760025147051649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14256301031360067058804397 5346112886760025147051649)
                ·
                  refine ⟨4009584665070018860288737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5346112886760025147051649 4009584665070018860288737)
                  ·
                    refine ⟨3007188498802514145216553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4009584665070018860288737 3007188498802514145216553)
                    ·
                      refine ⟨2255391374101885608912415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3007188498802514145216553 2255391374101885608912415)
                      ·
                        rfl

theorem cell23_4392359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_4392359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392359 prefixEnd_4392359 := by exact prefixLift 4392359
  have htrace : WordTrace (prefixWord ++ tailWord_4392359) baseStart_4392359 baseEnd_4392359 := by
    simpa [prefixWord, tailWord_4392359, baseEnd_4392359] using wordTrace_append hprefix tailTrace_4392359
  have hstable : (prefixWord ++ tailWord_4392359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392359).length < 2 ^ (prefixWord ++ tailWord_4392359).sum := by decide
  have hdescent : baseEnd_4392359 < baseStart_4392359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392428 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 4]
def baseStart_4392428 : Nat := 118140960795 + 4392428 * 2 ^ 59
def prefixEnd_4392428 : Nat := 4983230072969 + 3 ^ 40 * 4392428 * 2
def baseEnd_4392428 : Nat := 2255426804267045838949597

theorem tailTrace_4392428 : CollatzResearch.WordTrace tailWord_4392428 prefixEnd_4392428 2255426804267045838949597 := by
  unfold tailWord_4392428
  simp only [CollatzResearch.WordTrace]
  refine ⟨80102505265495498911832969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106803340353993998549110625 80102505265495498911832969)
  ·
    refine ⟨60076878949121624183874727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80102505265495498911832969 60076878949121624183874727)
    ·
      refine ⟨90115318423682436275812091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60076878949121624183874727 90115318423682436275812091)
      ·
        refine ⟨135172977635523654413718137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90115318423682436275812091 135172977635523654413718137)
        ·
          refine ⟨101379733226642740810288603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135172977635523654413718137 101379733226642740810288603)
          ·
            refine ⟨152069599839964111215432905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101379733226642740810288603 152069599839964111215432905)
            ·
              refine ⟨114052199879973083411574679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152069599839964111215432905 114052199879973083411574679)
              ·
                refine ⟨171078299819959625117362019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114052199879973083411574679 171078299819959625117362019)
                ·
                  refine ⟨256617449729939437676043029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 171078299819959625117362019 256617449729939437676043029)
                  ·
                    refine ⟨12028942956090911141064517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 256617449729939437676043029 12028942956090911141064517)
                    ·
                      refine ⟨2255426804267045838949597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12028942956090911141064517 2255426804267045838949597)
                      ·
                        rfl

theorem cell23_4392428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 4].length) (baseStart_4392428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392428 prefixEnd_4392428 := by exact prefixLift 4392428
  have htrace : WordTrace (prefixWord ++ tailWord_4392428) baseStart_4392428 baseEnd_4392428 := by
    simpa [prefixWord, tailWord_4392428, baseEnd_4392428] using wordTrace_append hprefix tailTrace_4392428
  have hstable : (prefixWord ++ tailWord_4392428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392428).length < 2 ^ (prefixWord ++ tailWord_4392428).sum := by decide
  have hdescent : baseEnd_4392428 < baseStart_4392428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392429 : List Nat := [1, 5, 1, 3, 2, 2, 1, 1, 2, 5]
def baseStart_4392429 : Nat := 118140960795 + 4392429 * 2 ^ 59
def prefixEnd_4392429 : Nat := 4983230072969 + 3 ^ 40 * 4392429 * 2
def baseEnd_4392429 : Nat := 751809105915900111679031

theorem tailTrace_4392429 : CollatzResearch.WordTrace tailWord_4392429 prefixEnd_4392429 751809105915900111679031 := by
  unfold tailWord_4392429
  simp only [CollatzResearch.WordTrace]
  refine ⟨160205047003987374994452341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106803364669324916662968227 160205047003987374994452341)
  ·
    refine ⟨15019223156623816405729907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 160205047003987374994452341 15019223156623816405729907)
    ·
      refine ⟨22528834734935724608594861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15019223156623816405729907 22528834734935724608594861)
      ·
        refine ⟨8448313025600896728223073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22528834734935724608594861 8448313025600896728223073)
        ·
          refine ⟨6336234769200672546167305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8448313025600896728223073 6336234769200672546167305)
          ·
            refine ⟨4752176076900504409625479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6336234769200672546167305 4752176076900504409625479)
            ·
              refine ⟨7128264115350756614438219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4752176076900504409625479 7128264115350756614438219)
              ·
                refine ⟨10692396173026134921657329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7128264115350756614438219 10692396173026134921657329)
                ·
                  refine ⟨8019297129769601191242997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10692396173026134921657329 8019297129769601191242997)
                  ·
                    refine ⟨751809105915900111679031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8019297129769601191242997 751809105915900111679031)
                    ·
                      rfl

theorem cell23_4392429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_4392429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392429 prefixEnd_4392429 := by exact prefixLift 4392429
  have htrace : WordTrace (prefixWord ++ tailWord_4392429) baseStart_4392429 baseEnd_4392429 := by
    simpa [prefixWord, tailWord_4392429, baseEnd_4392429] using wordTrace_append hprefix tailTrace_4392429
  have hstable : (prefixWord ++ tailWord_4392429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392429).length < 2 ^ (prefixWord ++ tailWord_4392429).sum := by decide
  have hdescent : baseEnd_4392429 < baseStart_4392429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392432 : List Nat := [2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 4]
def baseStart_4392432 : Nat := 118140960795 + 4392432 * 2 ^ 59
def prefixEnd_4392432 : Nat := 4983230072969 + 3 ^ 40 * 4392432 * 2
def baseEnd_4392432 : Nat := 2255428858189663823299579

theorem tailTrace_4392432 : CollatzResearch.WordTrace tailWord_4392432 prefixEnd_4392432 2255428858189663823299579 := by
  unfold tailWord_4392432
  simp only [CollatzResearch.WordTrace]
  refine ⟨80102578211488253253405775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106803437615317671004541033 80102578211488253253405775)
  ·
    refine ⟨120153867317232379880108663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80102578211488253253405775 120153867317232379880108663)
    ·
      refine ⟨180230800975848569820162995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120153867317232379880108663 180230800975848569820162995)
      ·
        refine ⟨270346201463772854730244493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180230800975848569820162995 270346201463772854730244493)
        ·
          refine ⟨101379825548914820523841685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 270346201463772854730244493 101379825548914820523841685)
          ·
            refine ⟨4752179322605382212055079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 101379825548914820523841685 4752179322605382212055079)
            ·
              refine ⟨7128268983908073318082619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4752179322605382212055079 7128268983908073318082619)
              ·
                refine ⟨10692403475862109977123929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7128268983908073318082619 10692403475862109977123929)
                ·
                  refine ⟨8019302606896582482842947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10692403475862109977123929 8019302606896582482842947)
                  ·
                    refine ⟨12028953910344873724264421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8019302606896582482842947 12028953910344873724264421)
                    ·
                      refine ⟨2255428858189663823299579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12028953910344873724264421 2255428858189663823299579)
                      ·
                        rfl

theorem cell23_4392432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 4].length) (baseStart_4392432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392432 prefixEnd_4392432 := by exact prefixLift 4392432
  have htrace : WordTrace (prefixWord ++ tailWord_4392432) baseStart_4392432 baseEnd_4392432 := by
    simpa [prefixWord, tailWord_4392432, baseEnd_4392432] using wordTrace_append hprefix tailTrace_4392432
  have hstable : (prefixWord ++ tailWord_4392432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392432).length < 2 ^ (prefixWord ++ tailWord_4392432).sum := by decide
  have hdescent : baseEnd_4392432 < baseStart_4392432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392435 : List Nat := [1, 1, 1, 2, 2, 2, 2, 5, 2, 2, 3]
def baseStart_4392435 : Nat := 118140960795 + 4392435 * 2 ^ 59
def prefixEnd_4392435 : Nat := 4983230072969 + 3 ^ 40 * 4392435 * 2
def baseEnd_4392435 : Nat := 2255430398631627311562065

theorem tailTrace_4392435 : CollatzResearch.WordTrace tailWord_4392435 prefixEnd_4392435 2255430398631627311562065 := by
  unfold tailWord_4392435
  simp only [CollatzResearch.WordTrace]
  refine ⟨160205265841965638019170759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106803510561310425346113839 160205265841965638019170759)
  ·
    refine ⟨240307898762948457028756139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160205265841965638019170759 240307898762948457028756139)
    ·
      refine ⟨360461848144422685543134209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240307898762948457028756139 360461848144422685543134209)
      ·
        refine ⟨270346386108317014157350657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 360461848144422685543134209 270346386108317014157350657)
        ·
          refine ⟨202759789581237760618012993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 270346386108317014157350657 202759789581237760618012993)
          ·
            refine ⟨152069842185928320463509745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202759789581237760618012993 152069842185928320463509745)
            ·
              refine ⟨114052381639446240347632309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152069842185928320463509745 114052381639446240347632309)
              ·
                refine ⟨10692410778698085032590529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 114052381639446240347632309 10692410778698085032590529)
                ·
                  refine ⟨8019308084023563774442897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10692410778698085032590529 8019308084023563774442897)
                  ·
                    refine ⟨6014481063017672830832173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8019308084023563774442897 6014481063017672830832173)
                    ·
                      refine ⟨2255430398631627311562065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6014481063017672830832173 2255430398631627311562065)
                      ·
                        rfl

theorem cell23_4392435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 2, 3].length) (baseStart_4392435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392435 prefixEnd_4392435 := by exact prefixLift 4392435
  have htrace : WordTrace (prefixWord ++ tailWord_4392435) baseStart_4392435 baseEnd_4392435 := by
    simpa [prefixWord, tailWord_4392435, baseEnd_4392435] using wordTrace_append hprefix tailTrace_4392435
  have hstable : (prefixWord ++ tailWord_4392435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392435).length < 2 ^ (prefixWord ++ tailWord_4392435).sum := by decide
  have hdescent : baseEnd_4392435 < baseStart_4392435 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392455 : List Nat := [1, 1, 4, 3, 2, 2, 1, 1, 8]
def baseStart_4392455 : Nat := 118140960795 + 4392455 * 2 ^ 59
def prefixEnd_4392455 : Nat := 4983230072969 + 3 ^ 40 * 4392455 * 2
def baseEnd_4392455 : Nat := 250604518693857470367997

theorem tailTrace_4392455 : CollatzResearch.WordTrace tailWord_4392455 prefixEnd_4392455 250604518693857470367997 := by
  unfold tailWord_4392455
  simp only [CollatzResearch.WordTrace]
  refine ⟨160205995301893181434898819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106803996867928787623265879 160205995301893181434898819)
  ·
    refine ⟨240308992952839772152348229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160205995301893181434898819 240308992952839772152348229)
    ·
      refine ⟨45057936178657457278565293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 240308992952839772152348229 45057936178657457278565293)
      ·
        refine ⟨16896726066996546479461985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45057936178657457278565293 16896726066996546479461985)
        ·
          refine ⟨12672544550247409859596489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16896726066996546479461985 12672544550247409859596489)
          ·
            refine ⟨9504408412685557394697367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12672544550247409859596489 9504408412685557394697367)
            ·
              refine ⟨14256612619028336092046051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9504408412685557394697367 14256612619028336092046051)
              ·
                refine ⟨21384918928542504138069077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14256612619028336092046051 21384918928542504138069077)
                ·
                  refine ⟨250604518693857470367997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21384918928542504138069077 250604518693857470367997)
                  ·
                    rfl

theorem cell23_4392455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 8].length) (baseStart_4392455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392455 prefixEnd_4392455 := by exact prefixLift 4392455
  have htrace : WordTrace (prefixWord ++ tailWord_4392455) baseStart_4392455 baseEnd_4392455 := by
    simpa [prefixWord, tailWord_4392455, baseEnd_4392455] using wordTrace_append hprefix tailTrace_4392455
  have hstable : (prefixWord ++ tailWord_4392455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392455).length < 2 ^ (prefixWord ++ tailWord_4392455).sum := by decide
  have hdescent : baseEnd_4392455 < baseStart_4392455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392535 : List Nat := [1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 6]
def baseStart_4392535 : Nat := 118140960795 + 4392535 * 2 ^ 59
def prefixEnd_4392535 : Nat := 4983230072969 + 3 ^ 40 * 4392535 * 2
def baseEnd_4392535 : Nat := 2255481746697076920311605

theorem tailTrace_4392535 : CollatzResearch.WordTrace tailWord_4392535 prefixEnd_4392535 2255481746697076920311605 := by
  unfold tailWord_4392535
  simp only [CollatzResearch.WordTrace]
  refine ⟨160208913141603355097811059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106805942094402236731874039 160208913141603355097811059)
  ·
    refine ⟨240313369712405032646716589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160208913141603355097811059 240313369712405032646716589)
    ·
      refine ⟨90117513642151887242518721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 240313369712405032646716589 90117513642151887242518721)
      ·
        refine ⟨67588135231613915431889041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90117513642151887242518721 67588135231613915431889041)
        ·
          refine ⟨50691101423710436573916781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67588135231613915431889041 50691101423710436573916781)
          ·
            refine ⟨19009163033891413715218793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50691101423710436573916781 19009163033891413715218793)
            ·
              refine ⟨14256872275418560286414095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19009163033891413715218793 14256872275418560286414095)
              ·
                refine ⟨21385308413127840429621143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14256872275418560286414095 21385308413127840429621143)
                ·
                  refine ⟨32077962619691760644431715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21385308413127840429621143 32077962619691760644431715)
                  ·
                    refine ⟨48116943929537640966647573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32077962619691760644431715 48116943929537640966647573)
                    ·
                      refine ⟨2255481746697076920311605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48116943929537640966647573 2255481746697076920311605)
                      ·
                        rfl

theorem cell23_4392535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_4392535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392535 prefixEnd_4392535 := by exact prefixLift 4392535
  have htrace : WordTrace (prefixWord ++ tailWord_4392535) baseStart_4392535 baseEnd_4392535 := by
    simpa [prefixWord, tailWord_4392535, baseEnd_4392535] using wordTrace_append hprefix tailTrace_4392535
  have hstable : (prefixWord ++ tailWord_4392535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392535).length < 2 ^ (prefixWord ++ tailWord_4392535).sum := by decide
  have hdescent : baseEnd_4392535 < baseStart_4392535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392552 : List Nat := [2, 1, 4, 3, 1, 1, 1, 1, 3, 2, 4]
def baseStart_4392552 : Nat := 118140960795 + 4392552 * 2 ^ 59
def prefixEnd_4392552 : Nat := 4983230072969 + 3 ^ 40 * 4392552 * 2
def baseEnd_4392552 : Nat := 2255490475868203353799027

theorem tailTrace_4392552 : CollatzResearch.WordTrace tailWord_4392552 prefixEnd_4392552 2255490475868203353799027 := by
  unfold tailWord_4392552
  simp only [CollatzResearch.WordTrace]
  refine ⟨80104766591270883500589955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106806355455027844667453273 80104766591270883500589955)
  ·
    refine ⟨120157149886906325250884933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80104766591270883500589955 120157149886906325250884933)
    ·
      refine ⟨22529465603794935984540925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120157149886906325250884933 22529465603794935984540925)
      ·
        refine ⟨8448549601423100994202847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22529465603794935984540925 8448549601423100994202847)
        ·
          refine ⟨12672824402134651491304271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8448549601423100994202847 12672824402134651491304271)
          ·
            refine ⟨19009236603201977236956407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12672824402134651491304271 19009236603201977236956407)
            ·
              refine ⟨28513854904802965855434611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19009236603201977236956407 28513854904802965855434611)
              ·
                refine ⟨42770782357204448783151917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28513854904802965855434611 42770782357204448783151917)
                ·
                  refine ⟨16039043383951668293681969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42770782357204448783151917 16039043383951668293681969)
                  ·
                    refine ⟨12029282537963751220261477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16039043383951668293681969 12029282537963751220261477)
                    ·
                      refine ⟨2255490475868203353799027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12029282537963751220261477 2255490475868203353799027)
                      ·
                        rfl

theorem cell23_4392552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_4392552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392552 prefixEnd_4392552 := by exact prefixLift 4392552
  have htrace : WordTrace (prefixWord ++ tailWord_4392552) baseStart_4392552 baseEnd_4392552 := by
    simpa [prefixWord, tailWord_4392552, baseEnd_4392552] using wordTrace_append hprefix tailTrace_4392552
  have hstable : (prefixWord ++ tailWord_4392552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392552).length < 2 ^ (prefixWord ++ tailWord_4392552).sum := by decide
  have hdescent : baseEnd_4392552 < baseStart_4392552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392556 : List Nat := [2, 2, 1, 1, 3, 1, 1, 7, 1, 2, 2]
def baseStart_4392556 : Nat := 118140960795 + 4392556 * 2 ^ 59
def prefixEnd_4392556 : Nat := 4983230072969 + 3 ^ 40 * 4392556 * 2
def baseEnd_4392556 : Nat := 2255492529790821338149009

theorem tailTrace_4392556 : CollatzResearch.WordTrace tailWord_4392556 prefixEnd_4392556 2255492529790821338149009 := by
  unfold tailWord_4392556
  simp only [CollatzResearch.WordTrace]
  refine ⟨80104839537263637842162761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106806452716351517122883681 80104839537263637842162761)
  ·
    refine ⟨60078629652947728381622071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80104839537263637842162761 60078629652947728381622071)
    ·
      refine ⟨90117944479421592572433107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60078629652947728381622071 90117944479421592572433107)
      ·
        refine ⟨135176916719132388858649661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90117944479421592572433107 135176916719132388858649661)
        ·
          refine ⟨50691343769674645821993623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135176916719132388858649661 50691343769674645821993623)
          ·
            refine ⟨76037015654511968732990435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50691343769674645821993623 76037015654511968732990435)
            ·
              refine ⟨114055523481767953099485653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76037015654511968732990435 114055523481767953099485653)
              ·
                refine ⟨2673176331603936400769195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 114055523481767953099485653 2673176331603936400769195)
                ·
                  refine ⟨4009764497405904601153793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2673176331603936400769195 4009764497405904601153793)
                  ·
                    refine ⟨3007323373054428450865345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4009764497405904601153793 3007323373054428450865345)
                    ·
                      refine ⟨2255492529790821338149009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3007323373054428450865345 2255492529790821338149009)
                      ·
                        rfl

theorem cell23_4392556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 7, 1, 2, 2].length) (baseStart_4392556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392556 prefixEnd_4392556 := by exact prefixLift 4392556
  have htrace : WordTrace (prefixWord ++ tailWord_4392556) baseStart_4392556 baseEnd_4392556 := by
    simpa [prefixWord, tailWord_4392556, baseEnd_4392556] using wordTrace_append hprefix tailTrace_4392556
  have hstable : (prefixWord ++ tailWord_4392556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392556).length < 2 ^ (prefixWord ++ tailWord_4392556).sum := by decide
  have hdescent : baseEnd_4392556 < baseStart_4392556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392566 : List Nat := [5, 1, 1, 2, 2, 2, 2, 2, 2, 4]
def baseStart_4392566 : Nat := 118140960795 + 4392566 * 2 ^ 59
def prefixEnd_4392566 : Nat := 4983230072969 + 3 ^ 40 * 4392566 * 2
def baseEnd_4392566 : Nat := 751832554865788766341321

theorem tailTrace_4392566 : CollatzResearch.WordTrace tailWord_4392566 prefixEnd_4392566 751832554865788766341321 := by
  unfold tailWord_4392566
  simp only [CollatzResearch.WordTrace]
  refine ⟨10013127737780690462011847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106806695869660698261459701 10013127737780690462011847)
  ·
    refine ⟨15019691606671035693017771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10013127737780690462011847 15019691606671035693017771)
    ·
      refine ⟨22529537410006553539526657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15019691606671035693017771 22529537410006553539526657)
      ·
        refine ⟨16897153057504915154644993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22529537410006553539526657 16897153057504915154644993)
        ·
          refine ⟨12672864793128686365983745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16897153057504915154644993 12672864793128686365983745)
          ·
            refine ⟨9504648594846514774487809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12672864793128686365983745 9504648594846514774487809)
            ·
              refine ⟨7128486446134886080865857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9504648594846514774487809 7128486446134886080865857)
              ·
                refine ⟨5346364834601164560649393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7128486446134886080865857 5346364834601164560649393)
                ·
                  refine ⟨4009773625950873420487045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5346364834601164560649393 4009773625950873420487045)
                  ·
                    refine ⟨751832554865788766341321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4009773625950873420487045 751832554865788766341321)
                    ·
                      rfl

theorem cell23_4392566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_4392566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392566 prefixEnd_4392566 := by exact prefixLift 4392566
  have htrace : WordTrace (prefixWord ++ tailWord_4392566) baseStart_4392566 baseEnd_4392566 := by
    simpa [prefixWord, tailWord_4392566, baseEnd_4392566] using wordTrace_append hprefix tailTrace_4392566
  have hstable : (prefixWord ++ tailWord_4392566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392566).length < 2 ^ (prefixWord ++ tailWord_4392566).sum := by decide
  have hdescent : baseEnd_4392566 < baseStart_4392566 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392573 : List Nat := [1, 4, 1, 1, 4, 2, 1, 4, 1, 2, 2]
def baseStart_4392573 : Nat := 118140960795 + 4392573 * 2 ^ 59
def prefixEnd_4392573 : Nat := 4983230072969 + 3 ^ 40 * 4392573 * 2
def baseEnd_4392573 : Nat := 2255501258961947771636431

theorem tailTrace_4392573 : CollatzResearch.WordTrace tailWord_4392573 prefixEnd_4392573 2255501258961947771636431 := by
  unfold tailWord_4392573
  simp only [CollatzResearch.WordTrace]
  refine ⟨160210299115465687587694373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106806866076977125058462915 160210299115465687587694373)
  ·
    refine ⟨30039431084149816422692695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160210299115465687587694373 30039431084149816422692695)
    ·
      refine ⟨45059146626224724634039043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30039431084149816422692695 45059146626224724634039043)
      ·
        refine ⟨67588719939337086951058565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45059146626224724634039043 67588719939337086951058565)
        ·
          refine ⟨12672884988625703803323481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67588719939337086951058565 12672884988625703803323481)
          ·
            refine ⟨9504663741469277852492611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12672884988625703803323481 9504663741469277852492611)
            ·
              refine ⟨14256995612203916778738917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9504663741469277852492611 14256995612203916778738917)
              ·
                refine ⟨2673186677288234396013547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14256995612203916778738917 2673186677288234396013547)
                ·
                  refine ⟨4009780015932351594020321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2673186677288234396013547 4009780015932351594020321)
                  ·
                    refine ⟨3007335011949263695515241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4009780015932351594020321 3007335011949263695515241)
                    ·
                      refine ⟨2255501258961947771636431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3007335011949263695515241 2255501258961947771636431)
                      ·
                        rfl

theorem cell23_4392573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 4, 1, 2, 2].length) (baseStart_4392573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392573 prefixEnd_4392573 := by exact prefixLift 4392573
  have htrace : WordTrace (prefixWord ++ tailWord_4392573) baseStart_4392573 baseEnd_4392573 := by
    simpa [prefixWord, tailWord_4392573, baseEnd_4392573] using wordTrace_append hprefix tailTrace_4392573
  have hstable : (prefixWord ++ tailWord_4392573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392573).length < 2 ^ (prefixWord ++ tailWord_4392573).sum := by decide
  have hdescent : baseEnd_4392573 < baseStart_4392573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392599 : List Nat := [1, 1, 3, 3, 2, 2, 2, 1, 3, 3, 2]
def baseStart_4392599 : Nat := 118140960795 + 4392599 * 2 ^ 59
def prefixEnd_4392599 : Nat := 4983230072969 + 3 ^ 40 * 4392599 * 2
def baseEnd_4392599 : Nat := 2255514609458964669911311

theorem tailTrace_4392599 : CollatzResearch.WordTrace tailWord_4392599 prefixEnd_4392599 2255514609458964669911311 := by
  unfold tailWord_4392599
  simp only [CollatzResearch.WordTrace]
  refine ⟨160211247413371494028140851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106807498275580996018760567 160211247413371494028140851)
  ·
    refine ⟨240316871120057241042211277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160211247413371494028140851 240316871120057241042211277)
    ·
      refine ⟨90118826670021465390829229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 240316871120057241042211277 90118826670021465390829229)
      ·
        refine ⟨33794560001258049521560961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90118826670021465390829229 33794560001258049521560961)
        ·
          refine ⟨25345920000943537141170721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33794560001258049521560961 25345920000943537141170721)
          ·
            refine ⟨19009440000707652855878041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25345920000943537141170721 19009440000707652855878041)
            ·
              refine ⟨14257080000530739641908531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19009440000707652855878041 14257080000530739641908531)
              ·
                refine ⟨21385620000796109462862797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14257080000530739641908531 21385620000796109462862797)
                ·
                  refine ⟨8019607500298541048573549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21385620000796109462862797 8019607500298541048573549)
                  ·
                    refine ⟨3007352812611952893215081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8019607500298541048573549 3007352812611952893215081)
                    ·
                      refine ⟨2255514609458964669911311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3007352812611952893215081 2255514609458964669911311)
                      ·
                        rfl

theorem cell23_4392599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_4392599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392599 prefixEnd_4392599 := by exact prefixLift 4392599
  have htrace : WordTrace (prefixWord ++ tailWord_4392599) baseStart_4392599 baseEnd_4392599 := by
    simpa [prefixWord, tailWord_4392599, baseEnd_4392599] using wordTrace_append hprefix tailTrace_4392599
  have hstable : (prefixWord ++ tailWord_4392599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392599).length < 2 ^ (prefixWord ++ tailWord_4392599).sum := by decide
  have hdescent : baseEnd_4392599 < baseStart_4392599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392605 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 3, 8]
def baseStart_4392605 : Nat := 118140960795 + 4392605 * 2 ^ 59
def prefixEnd_4392605 : Nat := 4983230072969 + 3 ^ 40 * 4392605 * 2
def baseEnd_4392605 : Nat := 751839230114297215478761

theorem tailTrace_4392605 : CollatzResearch.WordTrace tailWord_4392605 prefixEnd_4392605 751839230114297215478761 := by
  unfold tailWord_4392605
  simp only [CollatzResearch.WordTrace]
  refine ⟨160211466251349757052859269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106807644167566504701906179 160211466251349757052859269)
  ·
    refine ⟨30039649922128079447411113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160211466251349757052859269 30039649922128079447411113)
    ·
      refine ⟨22529737441596059585558335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30039649922128079447411113 22529737441596059585558335)
      ·
        refine ⟨33794606162394089378337503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22529737441596059585558335 33794606162394089378337503)
        ·
          refine ⟨50691909243591134067506255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33794606162394089378337503 50691909243591134067506255)
          ·
            refine ⟨76037863865386701101259383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50691909243591134067506255 76037863865386701101259383)
            ·
              refine ⟨114056795798080051651889075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76037863865386701101259383 114056795798080051651889075)
              ·
                refine ⟨171085193697120077477833613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114056795798080051651889075 171085193697120077477833613)
                ·
                  refine ⟨64156947636420029054187605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 171085193697120077477833613 64156947636420029054187605)
                  ·
                    refine ⟨751839230114297215478761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 64156947636420029054187605 751839230114297215478761)
                    ·
                      rfl

theorem cell23_4392605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_4392605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392605 prefixEnd_4392605 := by exact prefixLift 4392605
  have htrace : WordTrace (prefixWord ++ tailWord_4392605) baseStart_4392605 baseEnd_4392605 := by
    simpa [prefixWord, tailWord_4392605, baseEnd_4392605] using wordTrace_append hprefix tailTrace_4392605
  have hstable : (prefixWord ++ tailWord_4392605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392605).length < 2 ^ (prefixWord ++ tailWord_4392605).sum := by decide
  have hdescent : baseEnd_4392605 < baseStart_4392605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392610 : List Nat := [3, 3, 1, 4, 1, 2, 2, 1, 1, 2, 3]
def baseStart_4392610 : Nat := 118140960795 + 4392610 * 2 ^ 59
def prefixEnd_4392610 : Nat := 4983230072969 + 3 ^ 40 * 4392610 * 2
def baseEnd_4392610 : Nat := 2255520257746164126873761

theorem tailTrace_4392610 : CollatzResearch.WordTrace tailWord_4392610 prefixEnd_4392610 2255520257746164126873761 := by
  unfold tailWord_4392610
  simp only [CollatzResearch.WordTrace]
  refine ⟨40052912154082910726697821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106807765744221095271194189 40052912154082910726697821)
  ·
    refine ⟨15019842057781091522511683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40052912154082910726697821 15019842057781091522511683)
    ·
      refine ⟨22529763086671637283767525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15019842057781091522511683 22529763086671637283767525)
      ·
        refine ⟨4224330578750931990706411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22529763086671637283767525 4224330578750931990706411)
        ·
          refine ⟨6336495868126397986059617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4224330578750931990706411 6336495868126397986059617)
          ·
            refine ⟨4752371901094798489544713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6336495868126397986059617 4752371901094798489544713)
            ·
              refine ⟨3564278925821098867158535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4752371901094798489544713 3564278925821098867158535)
              ·
                refine ⟨5346418388731648300737803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3564278925821098867158535 5346418388731648300737803)
                ·
                  refine ⟨8019627583097472451106705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5346418388731648300737803 8019627583097472451106705)
                  ·
                    refine ⟨6014720687323104338330029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8019627583097472451106705 6014720687323104338330029)
                    ·
                      refine ⟨2255520257746164126873761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6014720687323104338330029 2255520257746164126873761)
                      ·
                        rfl

theorem cell23_4392610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_4392610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392610 prefixEnd_4392610 := by exact prefixLift 4392610
  have htrace : WordTrace (prefixWord ++ tailWord_4392610) baseStart_4392610 baseEnd_4392610 := by
    simpa [prefixWord, tailWord_4392610, baseEnd_4392610] using wordTrace_append hprefix tailTrace_4392610
  have hstable : (prefixWord ++ tailWord_4392610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392610).length < 2 ^ (prefixWord ++ tailWord_4392610).sum := by decide
  have hdescent : baseEnd_4392610 < baseStart_4392610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392682 : List Nat := [3, 1, 3, 1, 1, 1, 3, 1, 4, 5]
def baseStart_4392682 : Nat := 118140960795 + 4392682 * 2 ^ 59
def prefixEnd_4392682 : Nat := 4983230072969 + 3 ^ 40 * 4392682 * 2
def baseEnd_4392682 : Nat := 751852409451095948391143

theorem tailTrace_4392682 : CollatzResearch.WordTrace tailWord_4392682 prefixEnd_4392682 751852409451095948391143 := by
  unfold tailWord_4392682
  simp only [CollatzResearch.WordTrace]
  refine ⟨40053568668017699800853075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106809516448047199468941533 40053568668017699800853075)
  ·
    refine ⟨60080353002026549701279613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40053568668017699800853075 60080353002026549701279613)
    ·
      refine ⟨22530132375759956137979855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60080353002026549701279613 22530132375759956137979855)
      ·
        refine ⟨33795198563639934206969783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22530132375759956137979855 33795198563639934206969783)
        ·
          refine ⟨50692797845459901310454675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33795198563639934206969783 50692797845459901310454675)
          ·
            refine ⟨76039196768189851965682013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50692797845459901310454675 76039196768189851965682013)
            ·
              refine ⟨28514698788071194487130755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76039196768189851965682013 28514698788071194487130755)
              ·
                refine ⟨42772048182106791730696133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28514698788071194487130755 42772048182106791730696133)
                ·
                  refine ⟨8019759034145023449505525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42772048182106791730696133 8019759034145023449505525)
                  ·
                    refine ⟨751852409451095948391143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8019759034145023449505525 751852409451095948391143)
                    ·
                      rfl

theorem cell23_4392682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_4392682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392682 prefixEnd_4392682 := by exact prefixLift 4392682
  have htrace : WordTrace (prefixWord ++ tailWord_4392682) baseStart_4392682 baseEnd_4392682 := by
    simpa [prefixWord, tailWord_4392682, baseEnd_4392682] using wordTrace_append hprefix tailTrace_4392682
  have hstable : (prefixWord ++ tailWord_4392682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392682).length < 2 ^ (prefixWord ++ tailWord_4392682).sum := by decide
  have hdescent : baseEnd_4392682 < baseStart_4392682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392686 : List Nat := [4, 1, 2, 1, 1, 2, 5, 2, 5]
def baseStart_4392686 : Nat := 118140960795 + 4392686 * 2 ^ 59
def prefixEnd_4392686 : Nat := 4983230072969 + 3 ^ 40 * 4392686 * 2
def baseEnd_4392686 : Nat := 250617698030656203280379

theorem tailTrace_4392686 : CollatzResearch.WordTrace tailWord_4392686 prefixEnd_4392686 250617698030656203280379 := by
  unfold tailWord_4392686
  simp only [CollatzResearch.WordTrace]
  refine ⟨20026802570507038485819739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106809613709370871924371941 20026802570507038485819739)
  ·
    refine ⟨30040203855760557728729609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20026802570507038485819739 30040203855760557728729609)
    ·
      refine ⟨22530152891820418296547207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30040203855760557728729609 22530152891820418296547207)
      ·
        refine ⟨33795229337730627444820811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22530152891820418296547207 33795229337730627444820811)
        ·
          refine ⟨50692844006595941167231217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33795229337730627444820811 50692844006595941167231217)
          ·
            refine ⟨38019633004946955875423413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50692844006595941167231217 38019633004946955875423413)
            ·
              refine ⟨3564340594213777113320945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38019633004946955875423413 3564340594213777113320945)
              ·
                refine ⟨2673255445660332834990709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3564340594213777113320945 2673255445660332834990709)
                ·
                  refine ⟨250617698030656203280379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2673255445660332834990709 250617698030656203280379)
                  ·
                    rfl

theorem cell23_4392686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 2, 5].length) (baseStart_4392686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392686 prefixEnd_4392686 := by exact prefixLift 4392686
  have htrace : WordTrace (prefixWord ++ tailWord_4392686) baseStart_4392686 baseEnd_4392686 := by
    simpa [prefixWord, tailWord_4392686, baseEnd_4392686] using wordTrace_append hprefix tailTrace_4392686
  have hstable : (prefixWord ++ tailWord_4392686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392686).length < 2 ^ (prefixWord ++ tailWord_4392686).sum := by decide
  have hdescent : baseEnd_4392686 < baseStart_4392686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392732 : List Nat := [2, 2, 3, 1, 1, 2, 2, 1, 2, 1, 6]
def baseStart_4392732 : Nat := 118140960795 + 4392732 * 2 ^ 59
def prefixEnd_4392732 : Nat := 4983230072969 + 3 ^ 40 * 4392732 * 2
def baseEnd_4392732 : Nat := 2255582902386012649548199

theorem tailTrace_4392732 : CollatzResearch.WordTrace tailWord_4392732 prefixEnd_4392732 2255582902386012649548199 := by
  unfold tailWord_4392732
  simp only [CollatzResearch.WordTrace]
  refine ⟨80108049160944828871366225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106810732214593105161821633 80108049160944828871366225)
  ·
    refine ⟨60081036870708621653524669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80108049160944828871366225 60081036870708621653524669)
    ·
      refine ⟨22530388826515733120071751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60081036870708621653524669 22530388826515733120071751)
      ·
        refine ⟨33795583239773599680107627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22530388826515733120071751 33795583239773599680107627)
        ·
          refine ⟨50693374859660399520161441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33795583239773599680107627 50693374859660399520161441)
          ·
            refine ⟨38020031144745299640121081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50693374859660399520161441 38020031144745299640121081)
            ·
              refine ⟨28515023358558974730090811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38020031144745299640121081 28515023358558974730090811)
              ·
                refine ⟨42772535037838462095136217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28515023358558974730090811 42772535037838462095136217)
                ·
                  refine ⟨32079401278378846571352163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42772535037838462095136217 32079401278378846571352163)
                  ·
                    refine ⟨48119101917568269857028245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32079401278378846571352163 48119101917568269857028245)
                    ·
                      refine ⟨2255582902386012649548199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48119101917568269857028245 2255582902386012649548199)
                      ·
                        rfl

theorem cell23_4392732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_4392732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392732 prefixEnd_4392732 := by exact prefixLift 4392732
  have htrace : WordTrace (prefixWord ++ tailWord_4392732) baseStart_4392732 baseEnd_4392732 := by
    simpa [prefixWord, tailWord_4392732, baseEnd_4392732] using wordTrace_append hprefix tailTrace_4392732
  have hstable : (prefixWord ++ tailWord_4392732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392732).length < 2 ^ (prefixWord ++ tailWord_4392732).sum := by decide
  have hdescent : baseEnd_4392732 < baseStart_4392732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392739 : List Nat := [1, 1, 1, 4, 2, 1, 4, 2, 2, 2, 3]
def baseStart_4392739 : Nat := 118140960795 + 4392739 * 2 ^ 59
def prefixEnd_4392739 : Nat := 4983230072969 + 3 ^ 40 * 4392739 * 2
def baseEnd_4392739 : Nat := 2255586496750594122160667

theorem tailTrace_4392739 : CollatzResearch.WordTrace tailWord_4392739 prefixEnd_4392739 2255586496750594122160667 := by
  unfold tailWord_4392739
  simp only [CollatzResearch.WordTrace]
  refine ⟨160216353632864297938237271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106810902421909531958824847 160216353632864297938237271)
  ·
    refine ⟨240324530449296446907355907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160216353632864297938237271 240324530449296446907355907)
    ·
      refine ⟨360486795673944670361033861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240324530449296446907355907 360486795673944670361033861)
      ·
        refine ⟨67591274188864625692693849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 360486795673944670361033861 67591274188864625692693849)
        ·
          refine ⟨50693455641648469269520387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67591274188864625692693849 50693455641648469269520387)
          ·
            refine ⟨76040183462472703904280581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50693455641648469269520387 76040183462472703904280581)
            ·
              refine ⟨14257534399213631982052609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76040183462472703904280581 14257534399213631982052609)
              ·
                refine ⟨10693150799410223986539457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14257534399213631982052609 10693150799410223986539457)
                ·
                  refine ⟨8019863099557667989904593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10693150799410223986539457 8019863099557667989904593)
                  ·
                    refine ⟨6014897324668250992428445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8019863099557667989904593 6014897324668250992428445)
                    ·
                      refine ⟨2255586496750594122160667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6014897324668250992428445 2255586496750594122160667)
                      ·
                        rfl

theorem cell23_4392739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 2, 2, 3].length) (baseStart_4392739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392739 prefixEnd_4392739 := by exact prefixLift 4392739
  have htrace : WordTrace (prefixWord ++ tailWord_4392739) baseStart_4392739 baseEnd_4392739 := by
    simpa [prefixWord, tailWord_4392739, baseEnd_4392739] using wordTrace_append hprefix tailTrace_4392739
  have hstable : (prefixWord ++ tailWord_4392739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392739).length < 2 ^ (prefixWord ++ tailWord_4392739).sum := by decide
  have hdescent : baseEnd_4392739 < baseStart_4392739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392752 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 3]
def baseStart_4392752 : Nat := 118140960795 + 4392752 * 2 ^ 59
def prefixEnd_4392752 : Nat := 4983230072969 + 3 ^ 40 * 4392752 * 2
def baseEnd_4392752 : Nat := 2255593171999102571298107

theorem tailTrace_4392752 : CollatzResearch.WordTrace tailWord_4392752 prefixEnd_4392752 2255593171999102571298107 := by
  unfold tailWord_4392752
  simp only [CollatzResearch.WordTrace]
  refine ⟨80108413890908600579230255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106811218521211467438973673 80108413890908600579230255)
  ·
    refine ⟨120162620836362900868845383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80108413890908600579230255 120162620836362900868845383)
    ·
      refine ⟨180243931254544351303268075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120162620836362900868845383 180243931254544351303268075)
      ·
        refine ⟨270365896881816526954902113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180243931254544351303268075 270365896881816526954902113)
        ·
          refine ⟨202774422661362395216176585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 270365896881816526954902113 202774422661362395216176585)
          ·
            refine ⟨152080816996021796412132439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202774422661362395216176585 152080816996021796412132439)
            ·
              refine ⟨228121225494032694618198659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152080816996021796412132439 228121225494032694618198659)
              ·
                refine ⟨342181838241049041927297989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 228121225494032694618198659 342181838241049041927297989)
                ·
                  refine ⟨64159094670196695361368373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 342181838241049041927297989 64159094670196695361368373)
                  ·
                    refine ⟨6014915125330940190128285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 64159094670196695361368373 6014915125330940190128285)
                    ·
                      refine ⟨2255593171999102571298107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6014915125330940190128285 2255593171999102571298107)
                      ·
                        rfl

theorem cell23_4392752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 3].length) (baseStart_4392752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392752 prefixEnd_4392752 := by exact prefixLift 4392752
  have htrace : WordTrace (prefixWord ++ tailWord_4392752) baseStart_4392752 baseEnd_4392752 := by
    simpa [prefixWord, tailWord_4392752, baseEnd_4392752] using wordTrace_append hprefix tailTrace_4392752
  have hstable : (prefixWord ++ tailWord_4392752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392752).length < 2 ^ (prefixWord ++ tailWord_4392752).sum := by decide
  have hdescent : baseEnd_4392752 < baseStart_4392752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392782 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5]
def baseStart_4392782 : Nat := 118140960795 + 4392782 * 2 ^ 59
def prefixEnd_4392782 : Nat := 4983230072969 + 3 ^ 40 * 4392782 * 2
def baseEnd_4392782 : Nat := 2255608576418737453922969

theorem tailTrace_4392782 : CollatzResearch.WordTrace tailWord_4392782 prefixEnd_4392782 2255608576418737453922969 := by
  unfold tailWord_4392782
  simp only [CollatzResearch.WordTrace]
  refine ⟨20027240246463564535256575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106811947981139010854701733 20027240246463564535256575)
  ·
    refine ⟨30040860369695346802884863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20027240246463564535256575 30040860369695346802884863)
    ·
      refine ⟨45061290554543020204327295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30040860369695346802884863 45061290554543020204327295)
      ·
        refine ⟨67591935831814530306490943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45061290554543020204327295 67591935831814530306490943)
        ·
          refine ⟨101387903747721795459736415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67591935831814530306490943 101387903747721795459736415)
          ·
            refine ⟨152081855621582693189604623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101387903747721795459736415 152081855621582693189604623)
            ·
              refine ⟨228122783432374039784406935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152081855621582693189604623 228122783432374039784406935)
              ·
                refine ⟨342184175148561059676610403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 228122783432374039784406935 342184175148561059676610403)
                ·
                  refine ⟨513276262722841589514915605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 342184175148561059676610403 513276262722841589514915605)
                  ·
                    refine ⟨24059824815133199508511669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 513276262722841589514915605 24059824815133199508511669)
                    ·
                      refine ⟨2255608576418737453922969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24059824815133199508511669 2255608576418737453922969)
                      ·
                        rfl

theorem cell23_4392782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_4392782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392782 prefixEnd_4392782 := by exact prefixLift 4392782
  have htrace : WordTrace (prefixWord ++ tailWord_4392782) baseStart_4392782 baseEnd_4392782 := by
    simpa [prefixWord, tailWord_4392782, baseEnd_4392782] using wordTrace_append hprefix tailTrace_4392782
  have hstable : (prefixWord ++ tailWord_4392782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392782).length < 2 ^ (prefixWord ++ tailWord_4392782).sum := by decide
  have hdescent : baseEnd_4392782 < baseStart_4392782 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392803 : List Nat := [1, 1, 1, 5, 4, 1, 2, 1, 3, 1, 3]
def baseStart_4392803 : Nat := 118140960795 + 4392803 * 2 ^ 59
def prefixEnd_4392803 : Nat := 4983230072969 + 3 ^ 40 * 4392803 * 2
def baseEnd_4392803 : Nat := 2255619359512481871760373

theorem tailTrace_4392803 : CollatzResearch.WordTrace tailWord_4392803 prefixEnd_4392803 2255619359512481871760373 := by
  unfold tailWord_4392803
  simp only [CollatzResearch.WordTrace]
  refine ⟨160218687904632436868567063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106812458603088291245711375 160218687904632436868567063)
  ·
    refine ⟨240328031856948655302850595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160218687904632436868567063 240328031856948655302850595)
    ·
      refine ⟨360492047785422982954275893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240328031856948655302850595 360492047785422982954275893)
      ·
        refine ⟨33796129479883404651963365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 360492047785422982954275893 33796129479883404651963365)
        ·
          refine ⟨6336774277478138372243131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33796129479883404651963365 6336774277478138372243131)
          ·
            refine ⟨9505161416217207558364697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6336774277478138372243131 9505161416217207558364697)
            ·
              refine ⟨7128871062162905668773523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9505161416217207558364697 7128871062162905668773523)
              ·
                refine ⟨10693306593244358503160285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7128871062162905668773523 10693306593244358503160285)
                ·
                  refine ⟨4009989972466634438685107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10693306593244358503160285 4009989972466634438685107)
                  ·
                    refine ⟨6014984958699951658027661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4009989972466634438685107 6014984958699951658027661)
                    ·
                      refine ⟨2255619359512481871760373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6014984958699951658027661 2255619359512481871760373)
                      ·
                        rfl

theorem cell23_4392803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_4392803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392803 prefixEnd_4392803 := by exact prefixLift 4392803
  have htrace : WordTrace (prefixWord ++ tailWord_4392803) baseStart_4392803 baseEnd_4392803 := by
    simpa [prefixWord, tailWord_4392803, baseEnd_4392803] using wordTrace_append hprefix tailTrace_4392803
  have hstable : (prefixWord ++ tailWord_4392803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392803).length < 2 ^ (prefixWord ++ tailWord_4392803).sum := by decide
  have hdescent : baseEnd_4392803 < baseStart_4392803 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392832 : List Nat := [2, 1, 1, 2, 1, 2, 5, 9]
def baseStart_4392832 : Nat := 118140960795 + 4392832 * 2 ^ 59
def prefixEnd_4392832 : Nat := 4983230072969 + 3 ^ 40 * 4392832 * 2
def baseEnd_4392832 : Nat := 83542009275980083640657

theorem tailTrace_4392832 : CollatzResearch.WordTrace tailWord_4392832 prefixEnd_4392832 83542009275980083640657 := by
  unfold tailWord_4392832
  simp only [CollatzResearch.WordTrace]
  refine ⟨80109872810763687410686375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106813163747684916547581833 80109872810763687410686375)
  ·
    refine ⟨120164809216145531116029563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80109872810763687410686375 120164809216145531116029563)
    ·
      refine ⟨180247213824218296674044345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120164809216145531116029563 180247213824218296674044345)
      ·
        refine ⟨135185410368163722505533259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180247213824218296674044345 135185410368163722505533259)
        ·
          refine ⟨202778115552245583758299889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135185410368163722505533259 202778115552245583758299889)
          ·
            refine ⟨152083586664184187818724917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202778115552245583758299889 152083586664184187818724917)
            ·
              refine ⟨14257836249767267608005461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 152083586664184187818724917 14257836249767267608005461)
              ·
                refine ⟨83542009275980083640657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14257836249767267608005461 83542009275980083640657)
                ·
                  rfl

theorem cell23_4392832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 9].length) (baseStart_4392832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392832 prefixEnd_4392832 := by exact prefixLift 4392832
  have htrace : WordTrace (prefixWord ++ tailWord_4392832) baseStart_4392832 baseEnd_4392832 := by
    simpa [prefixWord, tailWord_4392832, baseEnd_4392832] using wordTrace_append hprefix tailTrace_4392832
  have hstable : (prefixWord ++ tailWord_4392832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392832).length < 2 ^ (prefixWord ++ tailWord_4392832).sum := by decide
  have hdescent : baseEnd_4392832 < baseStart_4392832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392854 : List Nat := [5, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3]
def baseStart_4392854 : Nat := 118140960795 + 4392854 * 2 ^ 59
def prefixEnd_4392854 : Nat := 4983230072969 + 3 ^ 40 * 4392854 * 2
def baseEnd_4392854 : Nat := 2255645547025861172222639

theorem tailTrace_4392854 : CollatzResearch.WordTrace tailWord_4392854 prefixEnd_4392854 2255645547025861172222639 := by
  unfold tailWord_4392854
  simp only [CollatzResearch.WordTrace]
  refine ⟨10013784251715479536167101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106813698684965115052449077 10013784251715479536167101)
  ·
    refine ⟨3755169094393304826062663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10013784251715479536167101 3755169094393304826062663)
    ·
      refine ⟨5632753641589957239093995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3755169094393304826062663 5632753641589957239093995)
      ·
        refine ⟨8449130462384935858640993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5632753641589957239093995 8449130462384935858640993)
        ·
          refine ⟨6336847846788701893980745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8449130462384935858640993 6336847846788701893980745)
          ·
            refine ⟨4752635885091526420485559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6336847846788701893980745 4752635885091526420485559)
            ·
              refine ⟨7128953827637289630728339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4752635885091526420485559 7128953827637289630728339)
              ·
                refine ⟨10693430741455934446092509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7128953827637289630728339 10693430741455934446092509)
                ·
                  refine ⟨4010036528045975417284691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10693430741455934446092509 4010036528045975417284691)
                  ·
                    refine ⟨6015054792068963125927037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4010036528045975417284691 6015054792068963125927037)
                    ·
                      refine ⟨2255645547025861172222639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6015054792068963125927037 2255645547025861172222639)
                      ·
                        rfl

theorem cell23_4392854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_4392854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392854 prefixEnd_4392854 := by exact prefixLift 4392854
  have htrace : WordTrace (prefixWord ++ tailWord_4392854) baseStart_4392854 baseEnd_4392854 := by
    simpa [prefixWord, tailWord_4392854, baseEnd_4392854] using wordTrace_append hprefix tailTrace_4392854
  have hstable : (prefixWord ++ tailWord_4392854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392854).length < 2 ^ (prefixWord ++ tailWord_4392854).sum := by decide
  have hdescent : baseEnd_4392854 < baseStart_4392854 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392860 : List Nat := [2, 2, 3, 3, 1, 1, 3, 1, 3, 2, 2]
def baseStart_4392860 : Nat := 118140960795 + 4392860 * 2 ^ 59
def prefixEnd_4392860 : Nat := 4983230072969 + 3 ^ 40 * 4392860 * 2
def baseEnd_4392860 : Nat := 2255648627909788148747611

theorem tailTrace_4392860 : CollatzResearch.WordTrace tailWord_4392860 prefixEnd_4392860 2255648627909788148747611 := by
  unfold tailWord_4392860
  simp only [CollatzResearch.WordTrace]
  refine ⟨80110383432712967801696017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106813844576950623735594689 80110383432712967801696017)
  ·
    refine ⟨60082787574534725851272013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80110383432712967801696017 60082787574534725851272013)
    ·
      refine ⟨22531045340450522194227005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60082787574534725851272013 22531045340450522194227005)
      ·
        refine ⟨8449142002668945822835127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22531045340450522194227005 8449142002668945822835127)
        ·
          refine ⟨12673713004003418734252691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8449142002668945822835127 12673713004003418734252691)
          ·
            refine ⟨19010569506005128101379037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12673713004003418734252691 19010569506005128101379037)
            ·
              refine ⟨7128963564751923038017139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19010569506005128101379037 7128963564751923038017139)
              ·
                refine ⟨10693445347127884557025709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7128963564751923038017139 10693445347127884557025709)
                ·
                  refine ⟨4010042005172956708884641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10693445347127884557025709 4010042005172956708884641)
                  ·
                    refine ⟨3007531503879717531663481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4010042005172956708884641 3007531503879717531663481)
                    ·
                      refine ⟨2255648627909788148747611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3007531503879717531663481 2255648627909788148747611)
                      ·
                        rfl

theorem cell23_4392860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_4392860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392860 prefixEnd_4392860 := by exact prefixLift 4392860
  have htrace : WordTrace (prefixWord ++ tailWord_4392860) baseStart_4392860 baseEnd_4392860 := by
    simpa [prefixWord, tailWord_4392860, baseEnd_4392860] using wordTrace_append hprefix tailTrace_4392860
  have hstable : (prefixWord ++ tailWord_4392860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392860).length < 2 ^ (prefixWord ++ tailWord_4392860).sum := by decide
  have hdescent : baseEnd_4392860 < baseStart_4392860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392866 : List Nat := [3, 3, 1, 2, 3, 1, 2, 8]
def baseStart_4392866 : Nat := 118140960795 + 4392866 * 2 ^ 59
def prefixEnd_4392866 : Nat := 4983230072969 + 3 ^ 40 * 4392866 * 2
def baseEnd_4392866 : Nat := 83542655881248708343429

theorem tailTrace_4392866 : CollatzResearch.WordTrace tailWord_4392866 prefixEnd_4392866 83542655881248708343429 := by
  unfold tailWord_4392866
  simp only [CollatzResearch.WordTrace]
  refine ⟨40055246425851049657027613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106813990468936132418740301 40055246425851049657027613)
  ·
    refine ⟨15020717409694143621385355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40055246425851049657027613 15020717409694143621385355)
    ·
      refine ⟨22531076114541215432078033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15020717409694143621385355 22531076114541215432078033)
      ·
        refine ⟨16898307085905911574058525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22531076114541215432078033 16898307085905911574058525)
        ·
          refine ⟨6336865157214716840271947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16898307085905911574058525 6336865157214716840271947)
          ·
            refine ⟨9505297735822075260407921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6336865157214716840271947 9505297735822075260407921)
            ·
              refine ⟨7128973301866556445305941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9505297735822075260407921 7128973301866556445305941)
              ·
                refine ⟨83542655881248708343429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7128973301866556445305941 83542655881248708343429)
                ·
                  rfl

theorem cell23_4392866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 8].length) (baseStart_4392866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392866 prefixEnd_4392866 := by exact prefixLift 4392866
  have htrace : WordTrace (prefixWord ++ tailWord_4392866) baseStart_4392866 baseEnd_4392866 := by
    simpa [prefixWord, tailWord_4392866, baseEnd_4392866] using wordTrace_append hprefix tailTrace_4392866
  have hstable : (prefixWord ++ tailWord_4392866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392866).length < 2 ^ (prefixWord ++ tailWord_4392866).sum := by decide
  have hdescent : baseEnd_4392866 < baseStart_4392866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392919 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 1, 6, 3]
def baseStart_4392919 : Nat := 118140960795 + 4392919 * 2 ^ 59
def prefixEnd_4392919 : Nat := 4983230072969 + 3 ^ 40 * 4392919 * 2
def baseEnd_4392919 : Nat := 2255678923268403417909839

theorem tailTrace_4392919 : CollatzResearch.WordTrace tailWord_4392919 prefixEnd_4392919 2255678923268403417909839 := by
  unfold tailWord_4392919
  simp only [CollatzResearch.WordTrace]
  refine ⟨160222918772212188679789811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106815279181474792453193207 160222918772212188679789811)
  ·
    refine ⟨240334378158318283019684717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160222918772212188679789811 240334378158318283019684717)
    ·
      refine ⟨90125391809369356132381769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 240334378158318283019684717 90125391809369356132381769)
      ·
        refine ⟨67594043857027017099286327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90125391809369356132381769 67594043857027017099286327)
        ·
          refine ⟨101391065785540525648929491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67594043857027017099286327 101391065785540525648929491)
          ·
            refine ⟨152086598678310788473394237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101391065785540525648929491 152086598678310788473394237)
            ·
              refine ⟨57032474504366545677522839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 152086598678310788473394237 57032474504366545677522839)
              ·
                refine ⟨85548711756549818516284259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57032474504366545677522839 85548711756549818516284259)
                ·
                  refine ⟨128323067634824727774426389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85548711756549818516284259 128323067634824727774426389)
                  ·
                    refine ⟨6015143795382409114426237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 128323067634824727774426389 6015143795382409114426237)
                    ·
                      refine ⟨2255678923268403417909839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6015143795382409114426237 2255678923268403417909839)
                      ·
                        rfl

theorem cell23_4392919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 6, 3].length) (baseStart_4392919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392919 prefixEnd_4392919 := by exact prefixLift 4392919
  have htrace : WordTrace (prefixWord ++ tailWord_4392919) baseStart_4392919 baseEnd_4392919 := by
    simpa [prefixWord, tailWord_4392919, baseEnd_4392919] using wordTrace_append hprefix tailTrace_4392919
  have hstable : (prefixWord ++ tailWord_4392919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392919).length < 2 ^ (prefixWord ++ tailWord_4392919).sum := by decide
  have hdescent : baseEnd_4392919 < baseStart_4392919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392929 : List Nat := [1, 2, 3, 1, 2, 1, 3, 1, 1, 4, 4]
def baseStart_4392929 : Nat := 118140960795 + 4392929 * 2 ^ 59
def prefixEnd_4392929 : Nat := 4983230072969 + 3 ^ 40 * 4392929 * 2
def baseEnd_4392929 : Nat := 2255684058074948378784793

theorem tailTrace_4392929 : CollatzResearch.WordTrace tailWord_4392929 prefixEnd_4392929 2255684058074948378784793 := by
  unfold tailWord_4392929
  simp only [CollatzResearch.WordTrace]
  refine ⟨160223283502175960387653841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106815522334783973591769227 160223283502175960387653841)
  ·
    refine ⟨120167462626631970290740381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160223283502175960387653841 120167462626631970290740381)
    ·
      refine ⟨45062798484986988859027643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120167462626631970290740381 45062798484986988859027643)
      ·
        refine ⟨67594197727480483288541465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45062798484986988859027643 67594197727480483288541465)
        ·
          refine ⟨50695648295610362466406099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67594197727480483288541465 50695648295610362466406099)
          ·
            refine ⟨76043472443415543699609149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50695648295610362466406099 76043472443415543699609149)
            ·
              refine ⟨28516302166280828887353431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76043472443415543699609149 28516302166280828887353431)
              ·
                refine ⟨42774453249421243331030147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28516302166280828887353431 42774453249421243331030147)
                ·
                  refine ⟨64161679874131864996545221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42774453249421243331030147 64161679874131864996545221)
                  ·
                    refine ⟨12030314976399724686852229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 64161679874131864996545221 12030314976399724686852229)
                    ·
                      refine ⟨2255684058074948378784793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12030314976399724686852229 2255684058074948378784793)
                      ·
                        rfl

theorem cell23_4392929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_4392929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392929 prefixEnd_4392929 := by exact prefixLift 4392929
  have htrace : WordTrace (prefixWord ++ tailWord_4392929) baseStart_4392929 baseEnd_4392929 := by
    simpa [prefixWord, tailWord_4392929, baseEnd_4392929] using wordTrace_append hprefix tailTrace_4392929
  have hstable : (prefixWord ++ tailWord_4392929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392929).length < 2 ^ (prefixWord ++ tailWord_4392929).sum := by decide
  have hdescent : baseEnd_4392929 < baseStart_4392929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392967 : List Nat := [1, 1, 4, 3, 1, 4, 1, 2, 2, 2, 2]
def baseStart_4392967 : Nat := 118140960795 + 4392967 * 2 ^ 59
def prefixEnd_4392967 : Nat := 4983230072969 + 3 ^ 40 * 4392967 * 2
def baseEnd_4392967 : Nat := 2255703570339819230109619

theorem tailTrace_4392967 : CollatzResearch.WordTrace tailWord_4392967 prefixEnd_4392967 2255703570339819230109619 := by
  unfold tailWord_4392967
  simp only [CollatzResearch.WordTrace]
  refine ⟨160224669476038292877537155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106816446317358861918358103 160224669476038292877537155)
  ·
    refine ⟨240337004214057439316305733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160224669476038292877537155 240337004214057439316305733)
    ·
      refine ⟨45063188290135769871807325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 240337004214057439316305733 45063188290135769871807325)
      ·
        refine ⟨16898695608800913701927747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45063188290135769871807325 16898695608800913701927747)
        ·
          refine ⟨25348043413201370552891621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16898695608800913701927747 25348043413201370552891621)
          ·
            refine ⟨4752758139975256978667179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25348043413201370552891621 4752758139975256978667179)
            ·
              refine ⟨7129137209962885468000769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4752758139975256978667179 7129137209962885468000769)
              ·
                refine ⟨5346852907472164101000577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7129137209962885468000769 5346852907472164101000577)
                ·
                  refine ⟨4010139680604123075750433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5346852907472164101000577 4010139680604123075750433)
                  ·
                    refine ⟨3007604760453092306812825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4010139680604123075750433 3007604760453092306812825)
                    ·
                      refine ⟨2255703570339819230109619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3007604760453092306812825 2255703570339819230109619)
                      ·
                        rfl

theorem cell23_4392967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_4392967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392967 prefixEnd_4392967 := by exact prefixLift 4392967
  have htrace : WordTrace (prefixWord ++ tailWord_4392967) baseStart_4392967 baseEnd_4392967 := by
    simpa [prefixWord, tailWord_4392967, baseEnd_4392967] using wordTrace_append hprefix tailTrace_4392967
  have hstable : (prefixWord ++ tailWord_4392967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392967).length < 2 ^ (prefixWord ++ tailWord_4392967).sum := by decide
  have hdescent : baseEnd_4392967 < baseStart_4392967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4392979 : List Nat := [1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 5]
def baseStart_4392979 : Nat := 118140960795 + 4392979 * 2 ^ 59
def prefixEnd_4392979 : Nat := 4983230072969 + 3 ^ 40 * 4392979 * 2
def baseEnd_4392979 : Nat := 2255709732107673183159563

theorem tailTrace_4392979 : CollatzResearch.WordTrace tailWord_4392979 prefixEnd_4392979 2255709732107673183159563 := by
  unfold tailWord_4392979
  simp only [CollatzResearch.WordTrace]
  refine ⟨160225107151994818926973991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106816738101329879284649327 160225107151994818926973991)
  ·
    refine ⟨240337660727992228390460987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160225107151994818926973991 240337660727992228390460987)
    ·
      refine ⟨360506491091988342585691481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240337660727992228390460987 360506491091988342585691481)
      ·
        refine ⟨270379868318991256939268611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 360506491091988342585691481 270379868318991256939268611)
        ·
          refine ⟨405569802478486885408902917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270379868318991256939268611 405569802478486885408902917)
          ·
            refine ⟨76044337964716291014169297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 405569802478486885408902917 76044337964716291014169297)
            ·
              refine ⟨57033253473537218260626973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76044337964716291014169297 57033253473537218260626973)
              ·
                refine ⟨21387470052576456847735115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57033253473537218260626973 21387470052576456847735115)
                ·
                  refine ⟨32081205078864685271602673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21387470052576456847735115 32081205078864685271602673)
                  ·
                    refine ⟨24060903809148513953702005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32081205078864685271602673 24060903809148513953702005)
                    ·
                      refine ⟨2255709732107673183159563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24060903809148513953702005 2255709732107673183159563)
                      ·
                        rfl

theorem cell23_4392979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 5].length) (baseStart_4392979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4392979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4392979 prefixEnd_4392979 := by exact prefixLift 4392979
  have htrace : WordTrace (prefixWord ++ tailWord_4392979) baseStart_4392979 baseEnd_4392979 := by
    simpa [prefixWord, tailWord_4392979, baseEnd_4392979] using wordTrace_append hprefix tailTrace_4392979
  have hstable : (prefixWord ++ tailWord_4392979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4392979).length < 2 ^ (prefixWord ++ tailWord_4392979).sum := by decide
  have hdescent : baseEnd_4392979 < baseStart_4392979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4392979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4393019 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 4]
def baseStart_4393019 : Nat := 118140960795 + 4393019 * 2 ^ 59
def prefixEnd_4393019 : Nat := 4983230072969 + 3 ^ 40 * 4393019 * 2
def baseEnd_4393019 : Nat := 2255730271333853026659379

theorem tailTrace_4393019 : CollatzResearch.WordTrace tailWord_4393019 prefixEnd_4393019 2255730271333853026659379 := by
  unfold tailWord_4393019
  simp only [CollatzResearch.WordTrace]
  refine ⟨160226566071849905758430111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106817710714566603838953407 160226566071849905758430111)
  ·
    refine ⟨240339849107774858637645167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160226566071849905758430111 240339849107774858637645167)
    ·
      refine ⟨360509773661662287956467751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240339849107774858637645167 360509773661662287956467751)
      ·
        refine ⟨540764660492493431934701627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 360509773661662287956467751 540764660492493431934701627)
        ·
          refine ⟨811146990738740147902052441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 540764660492493431934701627 811146990738740147902052441)
          ·
            refine ⟨608360243054055110926539331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 811146990738740147902052441 608360243054055110926539331)
            ·
              refine ⟨912540364581082666389808997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 608360243054055110926539331 912540364581082666389808997)
              ·
                refine ⟨171101318358952999948089187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 912540364581082666389808997 171101318358952999948089187)
                ·
                  refine ⟨256651977538429499922133781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 171101318358952999948089187 256651977538429499922133781)
                  ·
                    refine ⟨12030561447113882808850021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 256651977538429499922133781 12030561447113882808850021)
                    ·
                      refine ⟨2255730271333853026659379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12030561447113882808850021 2255730271333853026659379)
                      ·
                        rfl

theorem cell23_4393019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 4].length) (baseStart_4393019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4393019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4393019 prefixEnd_4393019 := by exact prefixLift 4393019
  have htrace : WordTrace (prefixWord ++ tailWord_4393019) baseStart_4393019 baseEnd_4393019 := by
    simpa [prefixWord, tailWord_4393019, baseEnd_4393019] using wordTrace_append hprefix tailTrace_4393019
  have hstable : (prefixWord ++ tailWord_4393019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4393019).length < 2 ^ (prefixWord ++ tailWord_4393019).sum := by decide
  have hdescent : baseEnd_4393019 < baseStart_4393019 := by decide
  rcases family_descends (prefixWord ++ tailWord_4393019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4393117 : List Nat := [1, 4, 2, 1, 1, 5, 1, 1, 2, 3, 2]
def baseStart_4393117 : Nat := 118140960795 + 4393117 * 2 ^ 59
def prefixEnd_4393117 : Nat := 4983230072969 + 3 ^ 40 * 4393117 * 2
def baseEnd_4393117 : Nat := 2255780592437993643233929

theorem tailTrace_4393117 : CollatzResearch.WordTrace tailWord_4393117 prefixEnd_4393117 2255780592437993643233929 := by
  unfold tailWord_4393117
  simp only [CollatzResearch.WordTrace]
  refine ⟨160230140425494868495497605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106820093616996578996998403 160230140425494868495497605)
  ·
    refine ⟨30043151329780287842905801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160230140425494868495497605 30043151329780287842905801)
    ·
      refine ⟨22532363497335215882179351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30043151329780287842905801 22532363497335215882179351)
      ·
        refine ⟨33798545246002823823269027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22532363497335215882179351 33798545246002823823269027)
        ·
          refine ⟨50697817869004235734903541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33798545246002823823269027 50697817869004235734903541)
          ·
            refine ⟨4752920425219147100147207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50697817869004235734903541 4752920425219147100147207)
            ·
              refine ⟨7129380637828720650220811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4752920425219147100147207 7129380637828720650220811)
              ·
                refine ⟨10694070956743080975331217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7129380637828720650220811 10694070956743080975331217)
                ·
                  refine ⟨8020553217557310731498413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10694070956743080975331217 8020553217557310731498413)
                  ·
                    refine ⟨3007707456583991524311905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8020553217557310731498413 3007707456583991524311905)
                    ·
                      refine ⟨2255780592437993643233929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3007707456583991524311905 2255780592437993643233929)
                      ·
                        rfl

theorem cell23_4393117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_4393117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4393117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4393117 prefixEnd_4393117 := by exact prefixLift 4393117
  have htrace : WordTrace (prefixWord ++ tailWord_4393117) baseStart_4393117 baseEnd_4393117 := by
    simpa [prefixWord, tailWord_4393117, baseEnd_4393117] using wordTrace_append hprefix tailTrace_4393117
  have hstable : (prefixWord ++ tailWord_4393117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4393117).length < 2 ^ (prefixWord ++ tailWord_4393117).sum := by decide
  have hdescent : baseEnd_4393117 < baseStart_4393117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4393117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4393124 : List Nat := [2, 3, 1, 2, 4, 1, 2, 3, 1, 1, 3]
def baseStart_4393124 : Nat := 118140960795 + 4393124 * 2 ^ 59
def prefixEnd_4393124 : Nat := 4983230072969 + 3 ^ 40 * 4393124 * 2
def baseEnd_4393124 : Nat := 2255784186802575115846397

theorem tailTrace_4393124 : CollatzResearch.WordTrace tailWord_4393124 prefixEnd_4393124 2255784186802575115846397 := by
  unfold tailWord_4393124
  simp only [CollatzResearch.WordTrace]
  refine ⟨80115197868234754345501213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106820263824313005794001617 80115197868234754345501213)
  ·
    refine ⟨30043199200588032879562955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80115197868234754345501213 30043199200588032879562955)
    ·
      refine ⟨45064798800882049319344433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30043199200588032879562955 45064798800882049319344433)
      ·
        refine ⟨33798599100661536989508325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45064798800882049319344433 33798599100661536989508325)
        ·
          refine ⟨6337237331374038185532811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33798599100661536989508325 6337237331374038185532811)
          ·
            refine ⟨9505855997061057278299217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6337237331374038185532811 9505855997061057278299217)
            ·
              refine ⟨7129391997795792958724413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9505855997061057278299217 7129391997795792958724413)
              ·
                refine ⟨2673521999173422359521655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7129391997795792958724413 2673521999173422359521655)
                ·
                  refine ⟨4010282998760133539282483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2673521999173422359521655 4010282998760133539282483)
                  ·
                    refine ⟨6015424498140200308923725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4010282998760133539282483 6015424498140200308923725)
                    ·
                      refine ⟨2255784186802575115846397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6015424498140200308923725 2255784186802575115846397)
                      ·
                        rfl

theorem cell23_4393124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 3, 1, 1, 3].length) (baseStart_4393124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4393124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4393124 prefixEnd_4393124 := by exact prefixLift 4393124
  have htrace : WordTrace (prefixWord ++ tailWord_4393124) baseStart_4393124 baseEnd_4393124 := by
    simpa [prefixWord, tailWord_4393124, baseEnd_4393124] using wordTrace_append hprefix tailTrace_4393124
  have hstable : (prefixWord ++ tailWord_4393124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4393124).length < 2 ^ (prefixWord ++ tailWord_4393124).sum := by decide
  have hdescent : baseEnd_4393124 < baseStart_4393124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4393124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4393147 : List Nat := [1, 1, 1, 1, 1, 2, 5, 6, 1, 2, 2]
def baseStart_4393147 : Nat := 118140960795 + 4393147 * 2 ^ 59
def prefixEnd_4393147 : Nat := 4983230072969 + 3 ^ 40 * 4393147 * 2
def baseEnd_4393147 : Nat := 2255795996857628525858791

theorem tailTrace_4393147 : CollatzResearch.WordTrace tailWord_4393147 prefixEnd_4393147 2255795996857628525858791 := by
  unfold tailWord_4393147
  simp only [CollatzResearch.WordTrace]
  refine ⟨160231234615386183619089695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106820823076924122412726463 160231234615386183619089695)
  ·
    refine ⟨240346851923079275428634543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160231234615386183619089695 240346851923079275428634543)
    ·
      refine ⟨360520277884618913142951815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240346851923079275428634543 360520277884618913142951815)
      ·
        refine ⟨540780416826928369714427723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 360520277884618913142951815 540780416826928369714427723)
        ·
          refine ⟨811170625240392554571641585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 540780416826928369714427723 811170625240392554571641585)
          ·
            refine ⟨608377968930294415928731189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 811170625240392554571641585 608377968930294415928731189)
            ·
              refine ⟨57035434587215101493318549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 608377968930294415928731189 57035434587215101493318549)
              ·
                refine ⟨2673535996275707882499307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 57035434587215101493318549 2673535996275707882499307)
                ·
                  refine ⟨4010303994413561823748961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2673535996275707882499307 4010303994413561823748961)
                  ·
                    refine ⟨3007727995810171367811721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4010303994413561823748961 3007727995810171367811721)
                    ·
                      refine ⟨2255795996857628525858791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3007727995810171367811721 2255795996857628525858791)
                      ·
                        rfl

theorem cell23_4393147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 6, 1, 2, 2].length) (baseStart_4393147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4393147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4393147 prefixEnd_4393147 := by exact prefixLift 4393147
  have htrace : WordTrace (prefixWord ++ tailWord_4393147) baseStart_4393147 baseEnd_4393147 := by
    simpa [prefixWord, tailWord_4393147, baseEnd_4393147] using wordTrace_append hprefix tailTrace_4393147
  have hstable : (prefixWord ++ tailWord_4393147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4393147).length < 2 ^ (prefixWord ++ tailWord_4393147).sum := by decide
  have hdescent : baseEnd_4393147 < baseStart_4393147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4393147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4393150 : List Nat := [4, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5]
def baseStart_4393150 : Nat := 118140960795 + 4393150 * 2 ^ 59
def prefixEnd_4393150 : Nat := 4983230072969 + 3 ^ 40 * 4393150 * 2
def baseEnd_4393150 : Nat := 2255797537299592014121277

theorem tailTrace_4393150 : CollatzResearch.WordTrace tailWord_4393150 prefixEnd_4393150 2255797537299592014121277 := by
  unfold tailWord_4393150
  simp only [CollatzResearch.WordTrace]
  refine ⟨20028918004296914391431113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106820896022916876754299269 20028918004296914391431113)
  ·
    refine ⟨15021688503222685793573335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20028918004296914391431113 15021688503222685793573335)
    ·
      refine ⟨22532532754834028690360003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15021688503222685793573335 22532532754834028690360003)
      ·
        refine ⟨33798799132251043035540005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22532532754834028690360003 33798799132251043035540005)
        ·
          refine ⟨6337274837297070569163751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33798799132251043035540005 6337274837297070569163751)
          ·
            refine ⟨9505912255945605853745627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6337274837297070569163751 9505912255945605853745627)
            ·
              refine ⟨14258868383918408780618441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9505912255945605853745627 14258868383918408780618441)
              ·
                refine ⟨10694151287938806585463831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14258868383918408780618441 10694151287938806585463831)
                ·
                  refine ⟨16041226931908209878195747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10694151287938806585463831 16041226931908209878195747)
                  ·
                    refine ⟨24061840397862314817293621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16041226931908209878195747 24061840397862314817293621)
                    ·
                      refine ⟨2255797537299592014121277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24061840397862314817293621 2255797537299592014121277)
                      ·
                        rfl

theorem cell23_4393150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_4393150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4393150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4393150 prefixEnd_4393150 := by exact prefixLift 4393150
  have htrace : WordTrace (prefixWord ++ tailWord_4393150) baseStart_4393150 baseEnd_4393150 := by
    simpa [prefixWord, tailWord_4393150, baseEnd_4393150] using wordTrace_append hprefix tailTrace_4393150
  have hstable : (prefixWord ++ tailWord_4393150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4393150).length < 2 ^ (prefixWord ++ tailWord_4393150).sum := by decide
  have hdescent : baseEnd_4393150 < baseStart_4393150 := by decide
  rcases family_descends (prefixWord ++ tailWord_4393150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4393170 : List Nat := [3, 2, 2, 2, 1, 4, 2, 7]
def baseStart_4393170 : Nat := 118140960795 + 4393170 * 2 ^ 59
def prefixEnd_4393170 : Nat := 4983230072969 + 3 ^ 40 * 4393170 * 2
def baseEnd_4393170 : Nat := 83548437293062293921155

theorem tailTrace_4393170 : CollatzResearch.WordTrace tailWord_4393170 prefixEnd_4393170 83548437293062293921155 := by
  unfold tailWord_4393170
  simp only [CollatzResearch.WordTrace]
  refine ⟨40058018373575714636794241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106821382329535239031451309 40058018373575714636794241)
  ·
    refine ⟨30043513780181785977595681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40058018373575714636794241 30043513780181785977595681)
    ·
      refine ⟨22532635335136339483196761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30043513780181785977595681 22532635335136339483196761)
      ·
        refine ⟨16899476501352254612397571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22532635335136339483196761 16899476501352254612397571)
        ·
          refine ⟨25349214752028381918596357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16899476501352254612397571 25349214752028381918596357)
          ·
            refine ⟨4752977766005321609736817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25349214752028381918596357 4752977766005321609736817)
            ·
              refine ⟨3564733324503991207302613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4752977766005321609736817 3564733324503991207302613)
              ·
                refine ⟨83548437293062293921155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3564733324503991207302613 83548437293062293921155)
                ·
                  rfl

theorem cell23_4393170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 7].length) (baseStart_4393170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4393170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4393170 prefixEnd_4393170 := by exact prefixLift 4393170
  have htrace : WordTrace (prefixWord ++ tailWord_4393170) baseStart_4393170 baseEnd_4393170 := by
    simpa [prefixWord, tailWord_4393170, baseEnd_4393170] using wordTrace_append hprefix tailTrace_4393170
  have hstable : (prefixWord ++ tailWord_4393170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4393170).length < 2 ^ (prefixWord ++ tailWord_4393170).sum := by decide
  have hdescent : baseEnd_4393170 < baseStart_4393170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4393170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4393181 : List Nat := [1, 4, 3, 2, 1, 1, 3, 3, 1, 2, 2]
def baseStart_4393181 : Nat := 118140960795 + 4393181 * 2 ^ 59
def prefixEnd_4393181 : Nat := 4983230072969 + 3 ^ 40 * 4393181 * 2
def baseEnd_4393181 : Nat := 2255813455199881392833635

theorem tailTrace_4393181 : CollatzResearch.WordTrace tailWord_4393181 prefixEnd_4393181 2255813455199881392833635 := by
  unfold tailWord_4393181
  simp only [CollatzResearch.WordTrace]
  refine ⟨160232474697263007425827397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106821649798175338283884931 160232474697263007425827397)
  ·
    refine ⟨30043589005736813892342637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160232474697263007425827397 30043589005736813892342637)
    ·
      refine ⟨11266345877151305209628489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30043589005736813892342637 11266345877151305209628489)
      ·
        refine ⟨8449759407863478907221367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11266345877151305209628489 8449759407863478907221367)
        ·
          refine ⟨12674639111795218360832051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8449759407863478907221367 12674639111795218360832051)
          ·
            refine ⟨19011958667692827541248077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12674639111795218360832051 19011958667692827541248077)
            ·
              refine ⟨7129484500384810327968029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19011958667692827541248077 7129484500384810327968029)
              ·
                refine ⟨2673556687644303872988011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7129484500384810327968029 2673556687644303872988011)
                ·
                  refine ⟨4010335031466455809482017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2673556687644303872988011 4010335031466455809482017)
                  ·
                    refine ⟨3007751273599841857111513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4010335031466455809482017 3007751273599841857111513)
                    ·
                      refine ⟨2255813455199881392833635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3007751273599841857111513 2255813455199881392833635)
                      ·
                        rfl

theorem cell23_4393181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_4393181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4393181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4393181 prefixEnd_4393181 := by exact prefixLift 4393181
  have htrace : WordTrace (prefixWord ++ tailWord_4393181) baseStart_4393181 baseEnd_4393181 := by
    simpa [prefixWord, tailWord_4393181, baseEnd_4393181] using wordTrace_append hprefix tailTrace_4393181
  have hstable : (prefixWord ++ tailWord_4393181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4393181).length < 2 ^ (prefixWord ++ tailWord_4393181).sum := by decide
  have hdescent : baseEnd_4393181 < baseStart_4393181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4393181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4393224 : List Nat := [2, 1, 3, 2, 3, 3, 1, 2, 1, 3, 2]
def baseStart_4393224 : Nat := 118140960795 + 4393224 * 2 ^ 59
def prefixEnd_4393224 : Nat := 4983230072969 + 3 ^ 40 * 4393224 * 2
def baseEnd_4393224 : Nat := 2255835534868024724595937

theorem tailTrace_4393224 : CollatzResearch.WordTrace tailWord_4393224 prefixEnd_4393224 2255835534868024724595937 := by
  unfold tailWord_4393224
  simp only [CollatzResearch.WordTrace]
  refine ⟨80117021518053612884821363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106822695357404817179761817 80117021518053612884821363)
  ·
    refine ⟨120175532277080419327232045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80117021518053612884821363 120175532277080419327232045)
    ·
      refine ⟨45065824603905157247712017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120175532277080419327232045 45065824603905157247712017)
      ·
        refine ⟨33799368452928867935784013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45065824603905157247712017 33799368452928867935784013)
        ·
          refine ⟨12674763169848325475919005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33799368452928867935784013 12674763169848325475919005)
          ·
            refine ⟨4753036188693122053469627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12674763169848325475919005 4753036188693122053469627)
            ·
              refine ⟨7129554283039683080204441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4753036188693122053469627 7129554283039683080204441)
              ·
                refine ⟨5347165712279762310153331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7129554283039683080204441 5347165712279762310153331)
                ·
                  refine ⟨8020748568419643465229997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5347165712279762310153331 8020748568419643465229997)
                  ·
                    refine ⟨3007780713157366299461249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8020748568419643465229997 3007780713157366299461249)
                    ·
                      refine ⟨2255835534868024724595937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3007780713157366299461249 2255835534868024724595937)
                      ·
                        rfl

theorem cell23_4393224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_4393224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4393224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4393224 prefixEnd_4393224 := by exact prefixLift 4393224
  have htrace : WordTrace (prefixWord ++ tailWord_4393224) baseStart_4393224 baseEnd_4393224 := by
    simpa [prefixWord, tailWord_4393224, baseEnd_4393224] using wordTrace_append hprefix tailTrace_4393224
  have hstable : (prefixWord ++ tailWord_4393224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4393224).length < 2 ^ (prefixWord ++ tailWord_4393224).sum := by decide
  have hdescent : baseEnd_4393224 < baseStart_4393224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4393224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4393330 : List Nat := [3, 2, 1, 2, 1, 3, 1, 2, 1, 4, 3]
def baseStart_4393330 : Nat := 118140960795 + 4393330 * 2 ^ 59
def prefixEnd_4393330 : Nat := 4983230072969 + 3 ^ 40 * 4393330 * 2
def baseEnd_4393330 : Nat := 2255889963817401309870449

theorem tailTrace_4393330 : CollatzResearch.WordTrace tailWord_4393330 prefixEnd_4393330 2255889963817401309870449 := by
  unfold tailWord_4393330
  simp only [CollatzResearch.WordTrace]
  refine ⟨40059477293430801468250361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106825272782482137248667629 40059477293430801468250361)
  ·
    refine ⟨30044607970073101101187771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40059477293430801468250361 30044607970073101101187771)
    ·
      refine ⟨45066911955109651651781657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30044607970073101101187771 45066911955109651651781657)
      ·
        refine ⟨33800183966332238738836243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45066911955109651651781657 33800183966332238738836243)
        ·
          refine ⟨50700275949498358108254365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33800183966332238738836243 50700275949498358108254365)
          ·
            refine ⟨19012603481061884290595387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50700275949498358108254365 19012603481061884290595387)
            ·
              refine ⟨28518905221592826435893081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19012603481061884290595387 28518905221592826435893081)
              ·
                refine ⟨21389178916194619826919811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28518905221592826435893081 21389178916194619826919811)
                ·
                  refine ⟨32083768374291929740379717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21389178916194619826919811 32083768374291929740379717)
                  ·
                    refine ⟨6015706570179736826321197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32083768374291929740379717 6015706570179736826321197)
                    ·
                      refine ⟨2255889963817401309870449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6015706570179736826321197 2255889963817401309870449)
                      ·
                        rfl

theorem cell23_4393330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_4393330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4393330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4393330 prefixEnd_4393330 := by exact prefixLift 4393330
  have htrace : WordTrace (prefixWord ++ tailWord_4393330) baseStart_4393330 baseEnd_4393330 := by
    simpa [prefixWord, tailWord_4393330, baseEnd_4393330] using wordTrace_append hprefix tailTrace_4393330
  have hstable : (prefixWord ++ tailWord_4393330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4393330).length < 2 ^ (prefixWord ++ tailWord_4393330).sum := by decide
  have hdescent : baseEnd_4393330 < baseStart_4393330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4393330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4393364 : List Nat := [2, 4, 2, 1, 3, 1, 1, 2, 2, 2, 3]
def baseStart_4393364 : Nat := 118140960795 + 4393364 * 2 ^ 59
def prefixEnd_4393364 : Nat := 4983230072969 + 3 ^ 40 * 4393364 * 2
def baseEnd_4393364 : Nat := 2255907422159654176845293

theorem tailTrace_4393364 : CollatzResearch.WordTrace tailWord_4393364 prefixEnd_4393364 2255907422159654176845293 := by
  unfold tailWord_4393364
  simp only [CollatzResearch.WordTrace]
  refine ⟨80119574627800014839869573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106826099503733353119826097 80119574627800014839869573)
  ·
    refine ⟨15022420242712502782475545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80119574627800014839869573 15022420242712502782475545)
    ·
      refine ⟨11266815182034377086856659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15022420242712502782475545 11266815182034377086856659)
      ·
        refine ⟨16900222773051565630284989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11266815182034377086856659 16900222773051565630284989)
        ·
          refine ⟨6337583539894337111356871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16900222773051565630284989 6337583539894337111356871)
          ·
            refine ⟨9506375309841505667035307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6337583539894337111356871 9506375309841505667035307)
            ·
              refine ⟨14259562964762258500552961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9506375309841505667035307 14259562964762258500552961)
              ·
                refine ⟨10694672223571693875414721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14259562964762258500552961 10694672223571693875414721)
                ·
                  refine ⟨8021004167678770406561041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10694672223571693875414721 8021004167678770406561041)
                  ·
                    refine ⟨6015753125759077804920781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8021004167678770406561041 6015753125759077804920781)
                    ·
                      refine ⟨2255907422159654176845293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6015753125759077804920781 2255907422159654176845293)
                      ·
                        rfl

theorem cell23_4393364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_4393364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4393364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4393364 prefixEnd_4393364 := by exact prefixLift 4393364
  have htrace : WordTrace (prefixWord ++ tailWord_4393364) baseStart_4393364 baseEnd_4393364 := by
    simpa [prefixWord, tailWord_4393364, baseEnd_4393364] using wordTrace_append hprefix tailTrace_4393364
  have hstable : (prefixWord ++ tailWord_4393364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4393364).length < 2 ^ (prefixWord ++ tailWord_4393364).sum := by decide
  have hdescent : baseEnd_4393364 < baseStart_4393364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4393364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4393384 : List Nat := [2, 1, 6, 1, 1, 1, 4, 1, 6]
def baseStart_4393384 : Nat := 118140960795 + 4393384 * 2 ^ 59
def prefixEnd_4393384 : Nat := 4983230072969 + 3 ^ 40 * 4393384 * 2
def baseEnd_4393384 : Nat := 250657521308082677621689

theorem tailTrace_4393384 : CollatzResearch.WordTrace tailWord_4393384 prefixEnd_4393384 250657521308082677621689 := by
  unfold tailWord_4393384
  simp only [CollatzResearch.WordTrace]
  refine ⟨80119939357763786547733603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106826585810351715396978137 80119939357763786547733603)
  ·
    refine ⟨120179909036645679821600405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80119939357763786547733603 120179909036645679821600405)
    ·
      refine ⟨5633433236092766241637519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 120179909036645679821600405 5633433236092766241637519)
      ·
        refine ⟨8450149854139149362456279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5633433236092766241637519 8450149854139149362456279)
        ·
          refine ⟨12675224781208724043684419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8450149854139149362456279 12675224781208724043684419)
          ·
            refine ⟨19012837171813086065526629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12675224781208724043684419 19012837171813086065526629)
            ·
              refine ⟨3564906969714953637286243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19012837171813086065526629 3564906969714953637286243)
              ·
                refine ⟨5347360454572430455929365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3564906969714953637286243 5347360454572430455929365)
                ·
                  refine ⟨250657521308082677621689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5347360454572430455929365 250657521308082677621689)
                  ·
                    rfl

theorem cell23_4393384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 6].length) (baseStart_4393384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4393384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4393384 prefixEnd_4393384 := by exact prefixLift 4393384
  have htrace : WordTrace (prefixWord ++ tailWord_4393384) baseStart_4393384 baseEnd_4393384 := by
    simpa [prefixWord, tailWord_4393384, baseEnd_4393384] using wordTrace_append hprefix tailTrace_4393384
  have hstable : (prefixWord ++ tailWord_4393384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4393384).length < 2 ^ (prefixWord ++ tailWord_4393384).sum := by decide
  have hdescent : baseEnd_4393384 < baseStart_4393384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4393384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4393397 : List Nat := [1, 3, 3, 2, 3, 1, 1, 1, 3, 5]
def baseStart_4393397 : Nat := 118140960795 + 4393397 * 2 ^ 59
def prefixEnd_4393397 : Nat := 4983230072969 + 3 ^ 40 * 4393397 * 2
def baseEnd_4393397 : Nat := 751974789007084182577547

theorem tailTrace_4393397 : CollatzResearch.WordTrace tailWord_4393397 prefixEnd_4393397 751974789007084182577547 := by
  unfold tailWord_4393397
  simp only [CollatzResearch.WordTrace]
  refine ⟨160240352864480476315690445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106826901909653650877126963 160240352864480476315690445)
  ·
    refine ⟨60090132324180178618383917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160240352864480476315690445 60090132324180178618383917)
    ·
      refine ⟨22533799621567566981893969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60090132324180178618383917 22533799621567566981893969)
      ·
        refine ⟨16900349716175675236420477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22533799621567566981893969 16900349716175675236420477)
        ·
          refine ⟨6337631143565878213657679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16900349716175675236420477 6337631143565878213657679)
          ·
            refine ⟨9506446715348817320486519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6337631143565878213657679 9506446715348817320486519)
            ·
              refine ⟨14259670073023225980729779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9506446715348817320486519 14259670073023225980729779)
              ·
                refine ⟨21389505109534838971094669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14259670073023225980729779 21389505109534838971094669)
                ·
                  refine ⟨8021064416075564614160501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21389505109534838971094669 8021064416075564614160501)
                  ·
                    refine ⟨751974789007084182577547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8021064416075564614160501 751974789007084182577547)
                    ·
                      rfl

theorem cell23_4393397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_4393397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4393397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4393397 prefixEnd_4393397 := by exact prefixLift 4393397
  have htrace : WordTrace (prefixWord ++ tailWord_4393397) baseStart_4393397 baseEnd_4393397 := by
    simpa [prefixWord, tailWord_4393397, baseEnd_4393397] using wordTrace_append hprefix tailTrace_4393397
  have hstable : (prefixWord ++ tailWord_4393397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4393397).length < 2 ^ (prefixWord ++ tailWord_4393397).sum := by decide
  have hdescent : baseEnd_4393397 < baseStart_4393397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4393397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4393404 : List Nat := [2, 2, 2, 4, 1, 1, 1, 3, 2, 3, 2]
def baseStart_4393404 : Nat := 118140960795 + 4393404 * 2 ^ 59
def prefixEnd_4393404 : Nat := 4983230072969 + 3 ^ 40 * 4393404 * 2
def baseEnd_4393404 : Nat := 2255927961385834020345109

theorem tailTrace_4393404 : CollatzResearch.WordTrace tailWord_4393404 prefixEnd_4393404 2255927961385834020345109 := by
  unfold tailWord_4393404
  simp only [CollatzResearch.WordTrace]
  refine ⟨80120304087727558255597633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106827072116970077674130177 80120304087727558255597633)
  ·
    refine ⟨60090228065795668691698225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80120304087727558255597633 60090228065795668691698225)
    ·
      refine ⟨45067671049346751518773669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60090228065795668691698225 45067671049346751518773669)
      ·
        refine ⟨8450188321752515909770063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45067671049346751518773669 8450188321752515909770063)
        ·
          refine ⟨12675282482628773864655095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8450188321752515909770063 12675282482628773864655095)
          ·
            refine ⟨19012923723943160796982643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12675282482628773864655095 19012923723943160796982643)
            ·
              refine ⟨28519385585914741195473965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19012923723943160796982643 28519385585914741195473965)
              ·
                refine ⟨10694769594718027948302737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28519385585914741195473965 10694769594718027948302737)
                ·
                  refine ⟨8021077196038520961227053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10694769594718027948302737 8021077196038520961227053)
                  ·
                    refine ⟨3007903948514445360460145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8021077196038520961227053 3007903948514445360460145)
                    ·
                      refine ⟨2255927961385834020345109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3007903948514445360460145 2255927961385834020345109)
                      ·
                        rfl

theorem cell23_4393404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_4393404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4393404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4393404 prefixEnd_4393404 := by exact prefixLift 4393404
  have htrace : WordTrace (prefixWord ++ tailWord_4393404) baseStart_4393404 baseEnd_4393404 := by
    simpa [prefixWord, tailWord_4393404, baseEnd_4393404] using wordTrace_append hprefix tailTrace_4393404
  have hstable : (prefixWord ++ tailWord_4393404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4393404).length < 2 ^ (prefixWord ++ tailWord_4393404).sum := by decide
  have hdescent : baseEnd_4393404 < baseStart_4393404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4393404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4393413 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 2, 5, 6]
def baseStart_4393413 : Nat := 118140960795 + 4393413 * 2 ^ 59
def prefixEnd_4393413 : Nat := 4983230072969 + 3 ^ 40 * 4393413 * 2
def baseEnd_4393413 : Nat := 2255932582711724485132567

theorem tailTrace_4393413 : CollatzResearch.WordTrace tailWord_4393413 prefixEnd_4393413 2255932582711724485132567 := by
  unfold tailWord_4393413
  simp only [CollatzResearch.WordTrace]
  refine ⟨160240936432422511048272893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106827290954948340698848595 160240936432422511048272893)
  ·
    refine ⟨60090351162158441643102335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160240936432422511048272893 60090351162158441643102335)
    ·
      refine ⟨90135526743237662464653503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60090351162158441643102335 90135526743237662464653503)
      ·
        refine ⟨135203290114856493696980255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90135526743237662464653503 135203290114856493696980255)
        ·
          refine ⟨202804935172284740545470383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135203290114856493696980255 202804935172284740545470383)
          ·
            refine ⟨304207402758427110818205575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202804935172284740545470383 304207402758427110818205575)
            ·
              refine ⟨456311104137640666227308363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304207402758427110818205575 456311104137640666227308363)
              ·
                refine ⟨684466656206460999340962545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 456311104137640666227308363 684466656206460999340962545)
                ·
                  refine ⟨513349992154845749505721909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 684466656206460999340962545 513349992154845749505721909)
                  ·
                    refine ⟨48126561764516789016161429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 513349992154845749505721909 48126561764516789016161429)
                    ·
                      refine ⟨2255932582711724485132567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48126561764516789016161429 2255932582711724485132567)
                      ·
                        rfl

theorem cell23_4393413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_4393413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4393413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4393413 prefixEnd_4393413 := by exact prefixLift 4393413
  have htrace : WordTrace (prefixWord ++ tailWord_4393413) baseStart_4393413 baseEnd_4393413 := by
    simpa [prefixWord, tailWord_4393413, baseEnd_4393413] using wordTrace_append hprefix tailTrace_4393413
  have hstable : (prefixWord ++ tailWord_4393413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4393413).length < 2 ^ (prefixWord ++ tailWord_4393413).sum := by decide
  have hdescent : baseEnd_4393413 < baseStart_4393413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4393413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4393428 : List Nat := [2, 4, 1, 2, 2, 1, 4, 2, 1, 1, 3]
def baseStart_4393428 : Nat := 118140960795 + 4393428 * 2 ^ 59
def prefixEnd_4393428 : Nat := 4983230072969 + 3 ^ 40 * 4393428 * 2
def baseEnd_4393428 : Nat := 2255940284921541926444999

theorem tailTrace_4393428 : CollatzResearch.WordTrace tailWord_4393428 prefixEnd_4393428 2255940284921541926444999 := by
  unfold tailWord_4393428
  simp only [CollatzResearch.WordTrace]
  refine ⟨80120741763684084305034469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106827655684912112406712625 80120741763684084305034469)
  ·
    refine ⟨15022639080690765807193963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80120741763684084305034469 15022639080690765807193963)
    ·
      refine ⟨22533958621036148710790945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15022639080690765807193963 22533958621036148710790945)
      ·
        refine ⟨16900468965777111533093209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22533958621036148710790945 16900468965777111533093209)
        ·
          refine ⟨12675351724332833649819907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16900468965777111533093209 12675351724332833649819907)
          ·
            refine ⟨19013027586499250474729861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12675351724332833649819907 19013027586499250474729861)
            ·
              refine ⟨3564942672468609464011849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19013027586499250474729861 3564942672468609464011849)
              ·
                refine ⟨2673707004351457098008887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3564942672468609464011849 2673707004351457098008887)
                ·
                  refine ⟨4010560506527185647013331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2673707004351457098008887 4010560506527185647013331)
                  ·
                    refine ⟨6015840759790778470519997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4010560506527185647013331 6015840759790778470519997)
                    ·
                      refine ⟨2255940284921541926444999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6015840759790778470519997 2255940284921541926444999)
                      ·
                        rfl

theorem cell23_4393428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_4393428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4393428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4393428 prefixEnd_4393428 := by exact prefixLift 4393428
  have htrace : WordTrace (prefixWord ++ tailWord_4393428) baseStart_4393428 baseEnd_4393428 := by
    simpa [prefixWord, tailWord_4393428, baseEnd_4393428] using wordTrace_append hprefix tailTrace_4393428
  have hstable : (prefixWord ++ tailWord_4393428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4393428).length < 2 ^ (prefixWord ++ tailWord_4393428).sum := by decide
  have hdescent : baseEnd_4393428 < baseStart_4393428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4393428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4393434 : List Nat := [3, 1, 1, 2, 3, 1, 2, 3, 3, 2, 2]
def baseStart_4393434 : Nat := 118140960795 + 4393434 * 2 ^ 59
def prefixEnd_4393434 : Nat := 4983230072969 + 3 ^ 40 * 4393434 * 2
def baseEnd_4393434 : Nat := 2255943365805468902969971

theorem tailTrace_4393434 : CollatzResearch.WordTrace tailWord_4393434 prefixEnd_4393434 2255943365805468902969971 := by
  unfold tailWord_4393434
  simp only [CollatzResearch.WordTrace]
  refine ⟨40060425591336607908696839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106827801576897621089858237 40060425591336607908696839)
  ·
    refine ⟨60090638387004911863045259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40060425591336607908696839 60090638387004911863045259)
    ·
      refine ⟨90135957580507367794567889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60090638387004911863045259 90135957580507367794567889)
      ·
        refine ⟨67601968185380525845925917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90135957580507367794567889 67601968185380525845925917)
        ·
          refine ⟨25350738069517697192222219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67601968185380525845925917 25350738069517697192222219)
          ·
            refine ⟨38026107104276545788333329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25350738069517697192222219 38026107104276545788333329)
            ·
              refine ⟨28519580328207409341249997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38026107104276545788333329 28519580328207409341249997)
              ·
                refine ⟨10694842623077778502968749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28519580328207409341249997 10694842623077778502968749)
                ·
                  refine ⟨4010565983654166938613281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10694842623077778502968749 4010565983654166938613281)
                  ·
                    refine ⟨3007924487740625203959961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4010565983654166938613281 3007924487740625203959961)
                    ·
                      refine ⟨2255943365805468902969971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3007924487740625203959961 2255943365805468902969971)
                      ·
                        rfl

theorem cell23_4393434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 3, 2, 2].length) (baseStart_4393434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4393434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4393434 prefixEnd_4393434 := by exact prefixLift 4393434
  have htrace : WordTrace (prefixWord ++ tailWord_4393434) baseStart_4393434 baseEnd_4393434 := by
    simpa [prefixWord, tailWord_4393434, baseEnd_4393434] using wordTrace_append hprefix tailTrace_4393434
  have hstable : (prefixWord ++ tailWord_4393434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4393434).length < 2 ^ (prefixWord ++ tailWord_4393434).sum := by decide
  have hdescent : baseEnd_4393434 < baseStart_4393434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4393434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4393437 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 5, 2, 3]
def baseStart_4393437 : Nat := 118140960795 + 4393437 * 2 ^ 59
def prefixEnd_4393437 : Nat := 4983230072969 + 3 ^ 40 * 4393437 * 2
def baseEnd_4393437 : Nat := 2255944906247432391232457

theorem tailTrace_4393437 : CollatzResearch.WordTrace tailWord_4393437 prefixEnd_4393437 2255944906247432391232457 := by
  unfold tailWord_4393437
  simp only [CollatzResearch.WordTrace]
  refine ⟨160241811784335563147146565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106827874522890375431431043 160241811784335563147146565)
  ·
    refine ⟨30045339709562918090089981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160241811784335563147146565 30045339709562918090089981)
    ·
      refine ⟨11267002391086094283783743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30045339709562918090089981 11267002391086094283783743)
      ·
        refine ⟨16900503586629141425675615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11267002391086094283783743 16900503586629141425675615)
        ·
          refine ⟨25350755379943712138513423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16900503586629141425675615 25350755379943712138513423)
          ·
            refine ⟨38026133069915568207770135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25350755379943712138513423 38026133069915568207770135)
            ·
              refine ⟨57039199604873352311655203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38026133069915568207770135 57039199604873352311655203)
              ·
                refine ⟨85558799407310028467482805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57039199604873352311655203 85558799407310028467482805)
                ·
                  refine ⟨8021137444435315168826513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 85558799407310028467482805 8021137444435315168826513)
                  ·
                    refine ⟨6015853083326486376619885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8021137444435315168826513 6015853083326486376619885)
                    ·
                      refine ⟨2255944906247432391232457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6015853083326486376619885 2255944906247432391232457)
                      ·
                        rfl

theorem cell23_4393437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_4393437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4393437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4393437 prefixEnd_4393437 := by exact prefixLift 4393437
  have htrace : WordTrace (prefixWord ++ tailWord_4393437) baseStart_4393437 baseEnd_4393437 := by
    simpa [prefixWord, tailWord_4393437, baseEnd_4393437] using wordTrace_append hprefix tailTrace_4393437
  have hstable : (prefixWord ++ tailWord_4393437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4393437).length < 2 ^ (prefixWord ++ tailWord_4393437).sum := by decide
  have hdescent : baseEnd_4393437 < baseStart_4393437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4393437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
