import V185TrunkScan23Chunk1027

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6085634 : List Nat := [3, 4, 1, 3, 1, 1, 2, 1, 1, 6]
def baseStart_6085634 : Nat := 118140960795 + 6085634 * 2 ^ 59
def prefixEnd_6085634 : Nat := 4983230072969 + 3 ^ 40 * 6085634 * 2
def baseEnd_6085634 : Nat := 1041618443114582720895895

theorem tailTrace_6085634 : CollatzResearch.WordTrace tailWord_6085634 prefixEnd_6085634 1041618443114582720895895 := by
  unfold tailWord_6085634
  simp only [CollatzResearch.WordTrace]
  refine ⟨55490326708698709096485989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147974204556529890923962637 55490326708698709096485989)
  ·
    refine ⟨10404436257881007955591123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55490326708698709096485989 10404436257881007955591123)
    ·
      refine ⟨15606654386821511933386685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10404436257881007955591123 15606654386821511933386685)
      ·
        refine ⟨5852495395058066975020007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15606654386821511933386685 5852495395058066975020007)
        ·
          refine ⟨8778743092587100462530011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5852495395058066975020007 8778743092587100462530011)
          ·
            refine ⟨13168114638880650693795017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8778743092587100462530011 13168114638880650693795017)
            ·
              refine ⟨9876085979160488020346263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13168114638880650693795017 9876085979160488020346263)
              ·
                refine ⟨14814128968740732030519395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9876085979160488020346263 14814128968740732030519395)
                ·
                  refine ⟨22221193453111098045779093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14814128968740732030519395 22221193453111098045779093)
                  ·
                    refine ⟨1041618443114582720895895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22221193453111098045779093 1041618443114582720895895)
                    ·
                      rfl

theorem cell23_6085634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_6085634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085634 prefixEnd_6085634 := by exact prefixLift 6085634
  have htrace : WordTrace (prefixWord ++ tailWord_6085634) baseStart_6085634 baseEnd_6085634 := by
    simpa [prefixWord, tailWord_6085634, baseEnd_6085634] using wordTrace_append hprefix tailTrace_6085634
  have hstable : (prefixWord ++ tailWord_6085634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085634).length < 2 ^ (prefixWord ++ tailWord_6085634).sum := by decide
  have hdescent : baseEnd_6085634 < baseStart_6085634 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6085640 : List Nat := [2, 1, 3, 2, 1, 3, 1, 3, 1, 3, 3]
def baseStart_6085640 : Nat := 118140960795 + 6085640 * 2 ^ 59
def prefixEnd_6085640 : Nat := 4983230072969 + 3 ^ 40 * 6085640 * 2
def baseEnd_6085640 : Nat := 3124858410227675139212657

theorem tailTrace_6085640 : CollatzResearch.WordTrace tailWord_6085640 prefixEnd_6085640 3124858410227675139212657 := by
  unfold tailWord_6085640
  simp only [CollatzResearch.WordTrace]
  refine ⟨110980762836386549705331187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147974350448515399607108249 110980762836386549705331187)
  ·
    refine ⟨166471144254579824557996781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110980762836386549705331187 166471144254579824557996781)
    ·
      refine ⟨62426679095467434209248793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166471144254579824557996781 62426679095467434209248793)
      ·
        refine ⟨46820009321600575656936595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62426679095467434209248793 46820009321600575656936595)
        ·
          refine ⟨70230013982400863485404893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46820009321600575656936595 70230013982400863485404893)
          ·
            refine ⟨26336255243400323807026835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70230013982400863485404893 26336255243400323807026835)
            ·
              refine ⟨39504382865100485710540253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26336255243400323807026835 39504382865100485710540253)
              ·
                refine ⟨14814143574412682141452595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39504382865100485710540253 14814143574412682141452595)
                ·
                  refine ⟨22221215361619023212178893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14814143574412682141452595 22221215361619023212178893)
                  ·
                    refine ⟨8332955760607133704567085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22221215361619023212178893 8332955760607133704567085)
                    ·
                      refine ⟨3124858410227675139212657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8332955760607133704567085 3124858410227675139212657)
                      ·
                        rfl

theorem cell23_6085640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_6085640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085640 prefixEnd_6085640 := by exact prefixLift 6085640
  have htrace : WordTrace (prefixWord ++ tailWord_6085640) baseStart_6085640 baseEnd_6085640 := by
    simpa [prefixWord, tailWord_6085640, baseEnd_6085640] using wordTrace_append hprefix tailTrace_6085640
  have hstable : (prefixWord ++ tailWord_6085640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085640).length < 2 ^ (prefixWord ++ tailWord_6085640).sum := by decide
  have hdescent : baseEnd_6085640 < baseStart_6085640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6085661 : List Nat := [1, 4, 2, 2, 3, 2, 2, 1, 1, 2, 3]
def baseStart_6085661 : Nat := 118140960795 + 6085661 * 2 ^ 59
def prefixEnd_6085661 : Nat := 4983230072969 + 3 ^ 40 * 6085661 * 2
def baseEnd_6085661 : Nat := 3124869193321419557050061

theorem tailTrace_6085661 : CollatzResearch.WordTrace tailWord_6085661 prefixEnd_6085661 3124869193321419557050061 := by
  unfold tailWord_6085661
  simp only [CollatzResearch.WordTrace]
  refine ⟨221962291605697019997176837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147974861070464679998117891 221962291605697019997176837)
  ·
    refine ⟨41617929676068191249470657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 221962291605697019997176837 41617929676068191249470657)
    ·
      refine ⟨31213447257051143437102993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41617929676068191249470657 31213447257051143437102993)
      ·
        refine ⟨23410085442788357577827245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31213447257051143437102993 23410085442788357577827245)
        ·
          refine ⟨8778782041045634091685217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23410085442788357577827245 8778782041045634091685217)
          ·
            refine ⟨6584086530784225568763913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8778782041045634091685217 6584086530784225568763913)
            ·
              refine ⟨4938064898088169176572935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6584086530784225568763913 4938064898088169176572935)
              ·
                refine ⟨7407097347132253764859403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4938064898088169176572935 7407097347132253764859403)
                ·
                  refine ⟨11110646020698380647289105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7407097347132253764859403 11110646020698380647289105)
                  ·
                    refine ⟨8332984515523785485466829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11110646020698380647289105 8332984515523785485466829)
                    ·
                      refine ⟨3124869193321419557050061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8332984515523785485466829 3124869193321419557050061)
                      ·
                        rfl

theorem cell23_6085661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_6085661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085661 prefixEnd_6085661 := by exact prefixLift 6085661
  have htrace : WordTrace (prefixWord ++ tailWord_6085661) baseStart_6085661 baseEnd_6085661 := by
    simpa [prefixWord, tailWord_6085661, baseEnd_6085661] using wordTrace_append hprefix tailTrace_6085661
  have hstable : (prefixWord ++ tailWord_6085661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085661).length < 2 ^ (prefixWord ++ tailWord_6085661).sum := by decide
  have hdescent : baseEnd_6085661 < baseStart_6085661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6085674 : List Nat := [3, 1, 4, 1, 3, 1, 1, 1, 4, 1, 3]
def baseStart_6085674 : Nat := 118140960795 + 6085674 * 2 ^ 59
def prefixEnd_6085674 : Nat := 4983230072969 + 3 ^ 40 * 6085674 * 2
def baseEnd_6085674 : Nat := 3124875868569928006187501

theorem tailTrace_6085674 : CollatzResearch.WordTrace tailWord_6085674 prefixEnd_6085674 3124875868569928006187501 := by
  unfold tailWord_6085674
  simp only [CollatzResearch.WordTrace]
  refine ⟨55490691438662480804350019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147975177169766615478266717 55490691438662480804350019)
  ·
    refine ⟨83236037157993721206525029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55490691438662480804350019 83236037157993721206525029)
    ·
      refine ⟨15606756967123822726223443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83236037157993721206525029 15606756967123822726223443)
      ·
        refine ⟨23410135450685734089335165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15606756967123822726223443 23410135450685734089335165)
        ·
          refine ⟨8778800794007150283500687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23410135450685734089335165 8778800794007150283500687)
          ·
            refine ⟨13168201191010725425251031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8778800794007150283500687 13168201191010725425251031)
            ·
              refine ⟨19752301786516088137876547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13168201191010725425251031 19752301786516088137876547)
              ·
                refine ⟨29628452679774132206814821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19752301786516088137876547 29628452679774132206814821)
                ·
                  refine ⟨5555334877457649788777779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29628452679774132206814821 5555334877457649788777779)
                  ·
                    refine ⟨8333002316186474683166669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5555334877457649788777779 8333002316186474683166669)
                    ·
                      refine ⟨3124875868569928006187501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8333002316186474683166669 3124875868569928006187501)
                      ·
                        rfl

theorem cell23_6085674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_6085674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085674 prefixEnd_6085674 := by exact prefixLift 6085674
  have htrace : WordTrace (prefixWord ++ tailWord_6085674) baseStart_6085674 baseEnd_6085674 := by
    simpa [prefixWord, tailWord_6085674, baseEnd_6085674] using wordTrace_append hprefix tailTrace_6085674
  have hstable : (prefixWord ++ tailWord_6085674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085674).length < 2 ^ (prefixWord ++ tailWord_6085674).sum := by decide
  have hdescent : baseEnd_6085674 < baseStart_6085674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6085683 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 5]
def baseStart_6085683 : Nat := 118140960795 + 6085683 * 2 ^ 59
def prefixEnd_6085683 : Nat := 4983230072969 + 3 ^ 40 * 6085683 * 2
def baseEnd_6085683 : Nat := 3124880489895818470974959

theorem tailTrace_6085683 : CollatzResearch.WordTrace tailWord_6085683 prefixEnd_6085683 3124880489895818470974959 := by
  unfold tailWord_6085683
  simp only [CollatzResearch.WordTrace]
  refine ⟨221963094011617317754477703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147975396007744878502985135 221963094011617317754477703)
  ·
    refine ⟨332944641017425976631716555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221963094011617317754477703 332944641017425976631716555)
    ·
      refine ⟨499416961526138964947574833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332944641017425976631716555 499416961526138964947574833)
      ·
        refine ⟨374562721144604223710681125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 499416961526138964947574833 374562721144604223710681125)
        ·
          refine ⟨70230510214613291945752711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 374562721144604223710681125 70230510214613291945752711)
          ·
            refine ⟨105345765321919937918629067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70230510214613291945752711 105345765321919937918629067)
            ·
              refine ⟨158018647982879906877943601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105345765321919937918629067 158018647982879906877943601)
              ·
                refine ⟨118513985987159930158457701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158018647982879906877943601 118513985987159930158457701)
                ·
                  refine ⟨22221372372592486904710819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 118513985987159930158457701 22221372372592486904710819)
                  ·
                    refine ⟨33332058558888730357066229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22221372372592486904710819 33332058558888730357066229)
                    ·
                      refine ⟨3124880489895818470974959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33332058558888730357066229 3124880489895818470974959)
                      ·
                        rfl

theorem cell23_6085683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 5].length) (baseStart_6085683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085683 prefixEnd_6085683 := by exact prefixLift 6085683
  have htrace : WordTrace (prefixWord ++ tailWord_6085683) baseStart_6085683 baseEnd_6085683 := by
    simpa [prefixWord, tailWord_6085683, baseEnd_6085683] using wordTrace_append hprefix tailTrace_6085683
  have hstable : (prefixWord ++ tailWord_6085683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085683).length < 2 ^ (prefixWord ++ tailWord_6085683).sum := by decide
  have hdescent : baseEnd_6085683 < baseStart_6085683 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6085714 : List Nat := [3, 2, 2, 1, 3, 1, 1, 2, 4, 2, 2]
def baseStart_6085714 : Nat := 118140960795 + 6085714 * 2 ^ 59
def prefixEnd_6085714 : Nat := 4983230072969 + 3 ^ 40 * 6085714 * 2
def baseEnd_6085714 : Nat := 3124896407796107849687317

theorem tailTrace_6085714 : CollatzResearch.WordTrace tailWord_6085714 prefixEnd_6085714 3124896407796107849687317 := by
  unfold tailWord_6085714
  simp only [CollatzResearch.WordTrace]
  refine ⟨55491056168626252512214049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147976149783003340032570797 55491056168626252512214049)
  ·
    refine ⟨41618292126469689384160537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55491056168626252512214049 41618292126469689384160537)
    ·
      refine ⟨31213719094852267038120403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41618292126469689384160537 31213719094852267038120403)
      ·
        refine ⟨46820578642278400557180605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31213719094852267038120403 46820578642278400557180605)
        ·
          refine ⟨17557716990854400208942727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46820578642278400557180605 17557716990854400208942727)
          ·
            refine ⟨26336575486281600313414091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17557716990854400208942727 26336575486281600313414091)
            ·
              refine ⟨39504863229422400470121137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26336575486281600313414091 39504863229422400470121137)
              ·
                refine ⟨29628647422066800352590853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39504863229422400470121137 29628647422066800352590853)
                ·
                  refine ⟨5555371391637525066110785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29628647422066800352590853 5555371391637525066110785)
                  ·
                    refine ⟨4166528543728143799583089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5555371391637525066110785 4166528543728143799583089)
                    ·
                      refine ⟨3124896407796107849687317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4166528543728143799583089 3124896407796107849687317)
                      ·
                        rfl

theorem cell23_6085714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_6085714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085714 prefixEnd_6085714 := by exact prefixLift 6085714
  have htrace : WordTrace (prefixWord ++ tailWord_6085714) baseStart_6085714 baseEnd_6085714 := by
    simpa [prefixWord, tailWord_6085714, baseEnd_6085714] using wordTrace_append hprefix tailTrace_6085714
  have hstable : (prefixWord ++ tailWord_6085714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085714).length < 2 ^ (prefixWord ++ tailWord_6085714).sum := by decide
  have hdescent : baseEnd_6085714 < baseStart_6085714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6085844 : List Nat := [2, 4, 1, 4, 1, 1, 1, 1, 8]
def baseStart_6085844 : Nat := 118140960795 + 6085844 * 2 ^ 59
def prefixEnd_6085844 : Nat := 4983230072969 + 3 ^ 40 * 6085844 * 2
def baseEnd_6085844 : Nat := 347218128920132482340191

theorem tailTrace_6085844 : CollatzResearch.WordTrace tailWord_6085844 prefixEnd_6085844 347218128920132482340191 := by
  unfold tailWord_6085844
  simp only [CollatzResearch.WordTrace]
  refine ⟨110984483082017021125544293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147979310776022694834059057 110984483082017021125544293)
  ·
    refine ⟨20809590577878191461039555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110984483082017021125544293 20809590577878191461039555)
    ·
      refine ⟨31214385866817287191559333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20809590577878191461039555 31214385866817287191559333)
      ·
        refine ⟨5852697350028241348417375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31214385866817287191559333 5852697350028241348417375)
        ·
          refine ⟨8779046025042362022626063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5852697350028241348417375 8779046025042362022626063)
          ·
            refine ⟨13168569037563543033939095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8779046025042362022626063 13168569037563543033939095)
            ·
              refine ⟨19752853556345314550908643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13168569037563543033939095 19752853556345314550908643)
              ·
                refine ⟨29629280334517971826362965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19752853556345314550908643 29629280334517971826362965)
                ·
                  refine ⟨347218128920132482340191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29629280334517971826362965 347218128920132482340191)
                  ·
                    rfl

theorem cell23_6085844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_6085844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085844 prefixEnd_6085844 := by exact prefixLift 6085844
  have htrace : WordTrace (prefixWord ++ tailWord_6085844) baseStart_6085844 baseEnd_6085844 := by
    simpa [prefixWord, tailWord_6085844, baseEnd_6085844] using wordTrace_append hprefix tailTrace_6085844
  have hstable : (prefixWord ++ tailWord_6085844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085844).length < 2 ^ (prefixWord ++ tailWord_6085844).sum := by decide
  have hdescent : baseEnd_6085844 < baseStart_6085844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6085887 : List Nat := [1, 1, 2, 2, 1, 5, 1, 2, 4, 4]
def baseStart_6085887 : Nat := 118140960795 + 6085887 * 2 ^ 59
def prefixEnd_6085887 : Nat := 4983230072969 + 3 ^ 40 * 6085887 * 2
def baseEnd_6085887 : Nat := 1041661746649778557608007

theorem tailTrace_6085887 : CollatzResearch.WordTrace tailWord_6085887 prefixEnd_6085887 1041661746649778557608007 := by
  unfold tailWord_6085887
  simp only [CollatzResearch.WordTrace]
  refine ⟨221970534502878260594903915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147980356335252173729935943 221970534502878260594903915)
  ·
    refine ⟨332955801754317390892355873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221970534502878260594903915 332955801754317390892355873)
    ·
      refine ⟨249716851315738043169266905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332955801754317390892355873 249716851315738043169266905)
      ·
        refine ⟨187287638486803532376950179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249716851315738043169266905 187287638486803532376950179)
        ·
          refine ⟨280931457730205298565425269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187287638486803532376950179 280931457730205298565425269)
          ·
            refine ⟨26337324162206746740508619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 280931457730205298565425269 26337324162206746740508619)
            ·
              refine ⟨39505986243310120110762929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26337324162206746740508619 39505986243310120110762929)
              ·
                refine ⟨29629489682482590083072197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39505986243310120110762929 29629489682482590083072197)
                ·
                  refine ⟨5555529315465485640576037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29629489682482590083072197 5555529315465485640576037)
                  ·
                    refine ⟨1041661746649778557608007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5555529315465485640576037 1041661746649778557608007)
                    ·
                      rfl

theorem cell23_6085887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 4, 4].length) (baseStart_6085887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085887 prefixEnd_6085887 := by exact prefixLift 6085887
  have htrace : WordTrace (prefixWord ++ tailWord_6085887) baseStart_6085887 baseEnd_6085887 := by
    simpa [prefixWord, tailWord_6085887, baseEnd_6085887] using wordTrace_append hprefix tailTrace_6085887
  have hstable : (prefixWord ++ tailWord_6085887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085887).length < 2 ^ (prefixWord ++ tailWord_6085887).sum := by decide
  have hdescent : baseEnd_6085887 < baseStart_6085887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6085897 : List Nat := [1, 2, 1, 1, 3, 3, 4, 1, 1, 1, 5]
def baseStart_6085897 : Nat := 118140960795 + 6085897 * 2 ^ 59
def prefixEnd_6085897 : Nat := 4983230072969 + 3 ^ 40 * 6085897 * 2
def baseEnd_6085897 : Nat := 3124990374755880633698975

theorem tailTrace_6085897 : CollatzResearch.WordTrace tailWord_6085897 prefixEnd_6085897 3124990374755880633698975 := by
  unfold tailWord_6085897
  simp only [CollatzResearch.WordTrace]
  refine ⟨221970899232842032302767945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147980599488561354868511963 221970899232842032302767945)
  ·
    refine ⟨166478174424631524227075959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221970899232842032302767945 166478174424631524227075959)
    ·
      refine ⟨249717261636947286340613939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166478174424631524227075959 249717261636947286340613939)
      ·
        refine ⟨374575892455420929510920909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249717261636947286340613939 374575892455420929510920909)
        ·
          refine ⟨140465959670782848566595341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 374575892455420929510920909 140465959670782848566595341)
          ·
            refine ⟨52674734876543568212473253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140465959670782848566595341 52674734876543568212473253)
            ·
              refine ⟨9876512789351919039838735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52674734876543568212473253 9876512789351919039838735)
              ·
                refine ⟨14814769184027878559758103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9876512789351919039838735 14814769184027878559758103)
                ·
                  refine ⟨22222153776041817839637155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14814769184027878559758103 22222153776041817839637155)
                  ·
                    refine ⟨33333230664062726759455733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22222153776041817839637155 33333230664062726759455733)
                    ·
                      refine ⟨3124990374755880633698975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33333230664062726759455733 3124990374755880633698975)
                      ·
                        rfl

theorem cell23_6085897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 1, 5].length) (baseStart_6085897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085897 prefixEnd_6085897 := by exact prefixLift 6085897
  have htrace : WordTrace (prefixWord ++ tailWord_6085897) baseStart_6085897 baseEnd_6085897 := by
    simpa [prefixWord, tailWord_6085897, baseEnd_6085897] using wordTrace_append hprefix tailTrace_6085897
  have hstable : (prefixWord ++ tailWord_6085897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085897).length < 2 ^ (prefixWord ++ tailWord_6085897).sum := by decide
  have hdescent : baseEnd_6085897 < baseStart_6085897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6085900 : List Nat := [2, 2, 1, 2, 2, 3, 11]
def baseStart_6085900 : Nat := 118140960795 + 6085900 * 2 ^ 59
def prefixEnd_6085900 : Nat := 4983230072969 + 3 ^ 40 * 6085900 * 2
def baseEnd_6085900 : Nat := 38580147101207952122981

theorem tailTrace_6085900 : CollatzResearch.WordTrace tailWord_6085900 prefixEnd_6085900 38580147101207952122981 := by
  unfold tailWord_6085900
  simp only [CollatzResearch.WordTrace]
  refine ⟨110985504325915581907563577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147980672434554109210084769 110985504325915581907563577)
  ·
    refine ⟨83239128244436686430672683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110985504325915581907563577 83239128244436686430672683)
    ·
      refine ⟨124858692366655029646009025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83239128244436686430672683 124858692366655029646009025)
      ·
        refine ⟨93644019274991272234506769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124858692366655029646009025 93644019274991272234506769)
        ·
          refine ⟨70233014456243454175880077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93644019274991272234506769 70233014456243454175880077)
          ·
            refine ⟨26337380421091295315955029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70233014456243454175880077 26337380421091295315955029)
            ·
              refine ⟨38580147101207952122981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 26337380421091295315955029 38580147101207952122981)
              ·
                rfl

theorem cell23_6085900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 11].length) (baseStart_6085900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085900 prefixEnd_6085900 := by exact prefixLift 6085900
  have htrace : WordTrace (prefixWord ++ tailWord_6085900) baseStart_6085900 baseEnd_6085900 := by
    simpa [prefixWord, tailWord_6085900, baseEnd_6085900] using wordTrace_append hprefix tailTrace_6085900
  have hstable : (prefixWord ++ tailWord_6085900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085900).length < 2 ^ (prefixWord ++ tailWord_6085900).sum := by decide
  have hdescent : baseEnd_6085900 < baseStart_6085900 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6085917 : List Nat := [1, 4, 2, 3, 1, 1, 1, 10]
def baseStart_6085917 : Nat := 118140960795 + 6085917 * 2 ^ 59
def prefixEnd_6085917 : Nat := 4983230072969 + 3 ^ 40 * 6085917 * 2
def baseEnd_6085917 : Nat := 115740764606258168720329

theorem tailTrace_6085917 : CollatzResearch.WordTrace tailWord_6085917 prefixEnd_6085917 115740764606258168720329 := by
  unfold tailWord_6085917
  simp only [CollatzResearch.WordTrace]
  refine ⟨221971628692769575718496005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147981085795179717145664003 221971628692769575718496005)
  ·
    refine ⟨41619680379894295447218001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 221971628692769575718496005 41619680379894295447218001)
    ·
      refine ⟨31214760284920721585413501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41619680379894295447218001 31214760284920721585413501)
      ·
        refine ⟨11705535106845270594530063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31214760284920721585413501 11705535106845270594530063)
        ·
          refine ⟨17558302660267905891795095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11705535106845270594530063 17558302660267905891795095)
          ·
            refine ⟨26337453990401858837692643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17558302660267905891795095 26337453990401858837692643)
            ·
              refine ⟨39506180985602788256538965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26337453990401858837692643 39506180985602788256538965)
              ·
                refine ⟨115740764606258168720329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 39506180985602788256538965 115740764606258168720329)
                ·
                  rfl

theorem cell23_6085917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 10].length) (baseStart_6085917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6085917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6085917 prefixEnd_6085917 := by exact prefixLift 6085917
  have htrace : WordTrace (prefixWord ++ tailWord_6085917) baseStart_6085917 baseEnd_6085917 := by
    simpa [prefixWord, tailWord_6085917, baseEnd_6085917] using wordTrace_append hprefix tailTrace_6085917
  have hstable : (prefixWord ++ tailWord_6085917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6085917).length < 2 ^ (prefixWord ++ tailWord_6085917).sum := by decide
  have hdescent : baseEnd_6085917 < baseStart_6085917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6085917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086024 : List Nat := [2, 1, 3, 3, 1, 3, 2, 1, 7]
def baseStart_6086024 : Nat := 118140960795 + 6086024 * 2 ^ 59
def prefixEnd_6086024 : Nat := 4983230072969 + 3 ^ 40 * 6086024 * 2
def baseEnd_6086024 : Nat := 347228398533222404090099

theorem tailTrace_6086024 : CollatzResearch.WordTrace tailWord_6086024 prefixEnd_6086024 347228398533222404090099 := by
  unfold tailWord_6086024
  simp only [CollatzResearch.WordTrace]
  refine ⟨110987765651690966496320563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147983687535587955328427417 110987765651690966496320563)
  ·
    refine ⟨166481648477536449744480845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110987765651690966496320563 166481648477536449744480845)
    ·
      refine ⟨62430618179076168654180317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166481648477536449744480845 62430618179076168654180317)
      ·
        refine ⟨23411481817153563245317619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62430618179076168654180317 23411481817153563245317619)
        ·
          refine ⟨35117222725730344867976429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23411481817153563245317619 35117222725730344867976429)
          ·
            refine ⟨13168958522148879325491161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35117222725730344867976429 13168958522148879325491161)
            ·
              refine ⟨9876718891611659494118371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13168958522148879325491161 9876718891611659494118371)
              ·
                refine ⟨14815078337417489241177557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9876718891611659494118371 14815078337417489241177557)
                ·
                  refine ⟨347228398533222404090099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14815078337417489241177557 347228398533222404090099)
                  ·
                    rfl

theorem cell23_6086024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 7].length) (baseStart_6086024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086024 prefixEnd_6086024 := by exact prefixLift 6086024
  have htrace : WordTrace (prefixWord ++ tailWord_6086024) baseStart_6086024 baseEnd_6086024 := by
    simpa [prefixWord, tailWord_6086024, baseEnd_6086024] using wordTrace_append hprefix tailTrace_6086024
  have hstable : (prefixWord ++ tailWord_6086024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086024).length < 2 ^ (prefixWord ++ tailWord_6086024).sum := by decide
  have hdescent : baseEnd_6086024 < baseStart_6086024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086037 : List Nat := [1, 3, 2, 1, 1, 2, 3, 2, 1, 7]
def baseStart_6086037 : Nat := 118140960795 + 6086037 * 2 ^ 59
def prefixEnd_6086037 : Nat := 4983230072969 + 3 ^ 40 * 6086037 * 2
def baseEnd_6086037 : Nat := 1041687420682503361982777

theorem tailTrace_6086037 : CollatzResearch.WordTrace tailWord_6086037 prefixEnd_6086037 1041687420682503361982777 := by
  unfold tailWord_6086037
  simp only [CollatzResearch.WordTrace]
  refine ⟨221976005452334836212864365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147984003634889890808576243 221976005452334836212864365)
  ·
    refine ⟨83241002044625563579824137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 221976005452334836212864365 83241002044625563579824137)
    ·
      refine ⟨62430751533469172684868103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83241002044625563579824137 62430751533469172684868103)
      ·
        refine ⟨93646127300203759027302155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62430751533469172684868103 93646127300203759027302155)
        ·
          refine ⟨140469190950305638540953233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93646127300203759027302155 140469190950305638540953233)
          ·
            refine ⟨105351893212729228905714925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140469190950305638540953233 105351893212729228905714925)
            ·
              refine ⟨39506959954773460839643097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105351893212729228905714925 39506959954773460839643097)
              ·
                refine ⟨29630219966080095629732323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39506959954773460839643097 29630219966080095629732323)
                ·
                  refine ⟨44445329949120143444598485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29630219966080095629732323 44445329949120143444598485)
                  ·
                    refine ⟨1041687420682503361982777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44445329949120143444598485 1041687420682503361982777)
                    ·
                      rfl

theorem cell23_6086037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_6086037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086037 prefixEnd_6086037 := by exact prefixLift 6086037
  have htrace : WordTrace (prefixWord ++ tailWord_6086037) baseStart_6086037 baseEnd_6086037 := by
    simpa [prefixWord, tailWord_6086037, baseEnd_6086037] using wordTrace_append hprefix tailTrace_6086037
  have hstable : (prefixWord ++ tailWord_6086037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086037).length < 2 ^ (prefixWord ++ tailWord_6086037).sum := by decide
  have hdescent : baseEnd_6086037 < baseStart_6086037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086094 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3]
def baseStart_6086094 : Nat := 118140960795 + 6086094 * 2 ^ 59
def prefixEnd_6086094 : Nat := 4983230072969 + 3 ^ 40 * 6086094 * 2
def baseEnd_6086094 : Nat := 3125091530444816362935569

theorem tailTrace_6086094 : CollatzResearch.WordTrace tailWord_6086094 prefixEnd_6086094 3125091530444816362935569 := by
  unfold tailWord_6086094
  simp only [CollatzResearch.WordTrace]
  refine ⟨27747260551641041868461167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 147985389608752223298459557 27747260551641041868461167)
  ·
    refine ⟨41620890827461562802691751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27747260551641041868461167 41620890827461562802691751)
    ·
      refine ⟨62431336241192344204037627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41620890827461562802691751 62431336241192344204037627)
      ·
        refine ⟨93647004361788516306056441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62431336241192344204037627 93647004361788516306056441)
        ·
          refine ⟨70235253271341387229542331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93647004361788516306056441 70235253271341387229542331)
          ·
            refine ⟨105352879907012080844313497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70235253271341387229542331 105352879907012080844313497)
            ·
              refine ⟨79014659930259060633235123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105352879907012080844313497 79014659930259060633235123)
              ·
                refine ⟨118521989895388590949852685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79014659930259060633235123 118521989895388590949852685)
                ·
                  refine ⟨44445746210770721606194757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118521989895388590949852685 44445746210770721606194757)
                  ·
                    refine ⟨8333577414519510301161517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44445746210770721606194757 8333577414519510301161517)
                    ·
                      refine ⟨3125091530444816362935569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8333577414519510301161517 3125091530444816362935569)
                      ·
                        rfl

theorem cell23_6086094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3].length) (baseStart_6086094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086094 prefixEnd_6086094 := by exact prefixLift 6086094
  have htrace : WordTrace (prefixWord ++ tailWord_6086094) baseStart_6086094 baseEnd_6086094 := by
    simpa [prefixWord, tailWord_6086094, baseEnd_6086094] using wordTrace_append hprefix tailTrace_6086094
  have hstable : (prefixWord ++ tailWord_6086094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086094).length < 2 ^ (prefixWord ++ tailWord_6086094).sum := by decide
  have hdescent : baseEnd_6086094 < baseStart_6086094 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086111 : List Nat := [1, 1, 2, 3, 3, 1, 4, 1, 2, 2, 3]
def baseStart_6086111 : Nat := 118140960795 + 6086111 * 2 ^ 59
def prefixEnd_6086111 : Nat := 4983230072969 + 3 ^ 40 * 6086111 * 2
def baseEnd_6086111 : Nat := 3125100259615942796422991

theorem tailTrace_6086111 : CollatzResearch.WordTrace tailWord_6086111 prefixEnd_6086111 3125100259615942796422991 := by
  unfold tailWord_6086111
  simp only [CollatzResearch.WordTrace]
  refine ⟨221978704454066746851058187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147985802969377831234038791 221978704454066746851058187)
  ·
    refine ⟨332968056681100120276587281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221978704454066746851058187 332968056681100120276587281)
    ·
      refine ⟨249726042510825090207440461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332968056681100120276587281 249726042510825090207440461)
      ·
        refine ⟨93647265941559408827790173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249726042510825090207440461 93647265941559408827790173)
        ·
          refine ⟨35117724728084778310421315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93647265941559408827790173 35117724728084778310421315)
          ·
            refine ⟨52676587092127167465631973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35117724728084778310421315 52676587092127167465631973)
            ·
              refine ⟨9876860079773843899805995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52676587092127167465631973 9876860079773843899805995)
              ·
                refine ⟨14815290119660765849708993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9876860079773843899805995 14815290119660765849708993)
                ·
                  refine ⟨11111467589745574387281745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14815290119660765849708993 11111467589745574387281745)
                  ·
                    refine ⟨8333600692309180790461309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11111467589745574387281745 8333600692309180790461309)
                    ·
                      refine ⟨3125100259615942796422991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8333600692309180790461309 3125100259615942796422991)
                      ·
                        rfl

theorem cell23_6086111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 2, 3].length) (baseStart_6086111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086111 prefixEnd_6086111 := by exact prefixLift 6086111
  have htrace : WordTrace (prefixWord ++ tailWord_6086111) baseStart_6086111 baseEnd_6086111 := by
    simpa [prefixWord, tailWord_6086111, baseEnd_6086111] using wordTrace_append hprefix tailTrace_6086111
  have hstable : (prefixWord ++ tailWord_6086111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086111).length < 2 ^ (prefixWord ++ tailWord_6086111).sum := by decide
  have hdescent : baseEnd_6086111 < baseStart_6086111 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086168 : List Nat := [2, 1, 2, 3, 4, 1, 1, 1, 1, 5, 2]
def baseStart_6086168 : Nat := 118140960795 + 6086168 * 2 ^ 59
def prefixEnd_6086168 : Nat := 4983230072969 + 3 ^ 40 * 6086168 * 2
def baseEnd_6086168 : Nat := 3125129528013249073410229

theorem tailTrace_6086168 : CollatzResearch.WordTrace tailWord_6086168 prefixEnd_6086168 3125129528013249073410229 := by
  unfold tailWord_6086168
  simp only [CollatzResearch.WordTrace]
  refine ⟨110990391707430122792941579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147987188943240163723922105 110990391707430122792941579)
  ·
    refine ⟨166485587561145184189412369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110990391707430122792941579 166485587561145184189412369)
    ·
      refine ⟨124864190670858888142059277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166485587561145184189412369 124864190670858888142059277)
      ·
        refine ⟨46824071501572083053272229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124864190670858888142059277 46824071501572083053272229)
        ·
          refine ⟨8779513406544765572488543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46824071501572083053272229 8779513406544765572488543)
          ·
            refine ⟨13169270109817148358732815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8779513406544765572488543 13169270109817148358732815)
            ·
              refine ⟨19753905164725722538099223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13169270109817148358732815 19753905164725722538099223)
              ·
                refine ⟨29630857747088583807148835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19753905164725722538099223 29630857747088583807148835)
                ·
                  refine ⟨44446286620632875710723253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29630857747088583807148835 44446286620632875710723253)
                  ·
                    refine ⟨4166839370684332097880305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44446286620632875710723253 4166839370684332097880305)
                    ·
                      refine ⟨3125129528013249073410229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4166839370684332097880305 3125129528013249073410229)
                      ·
                        rfl

theorem cell23_6086168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_6086168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086168 prefixEnd_6086168 := by exact prefixLift 6086168
  have htrace : WordTrace (prefixWord ++ tailWord_6086168) baseStart_6086168 baseEnd_6086168 := by
    simpa [prefixWord, tailWord_6086168, baseEnd_6086168] using wordTrace_append hprefix tailTrace_6086168
  have hstable : (prefixWord ++ tailWord_6086168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086168).length < 2 ^ (prefixWord ++ tailWord_6086168).sum := by decide
  have hdescent : baseEnd_6086168 < baseStart_6086168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086178 : List Nat := [3, 3, 1, 1, 1, 1, 6, 1, 1, 5]
def baseStart_6086178 : Nat := 118140960795 + 6086178 * 2 ^ 59
def prefixEnd_6086178 : Nat := 4983230072969 + 3 ^ 40 * 6086178 * 2
def baseEnd_6086178 : Nat := 1041711554273264678095061

theorem tailTrace_6086178 : CollatzResearch.WordTrace tailWord_6086178 prefixEnd_6086178 1041711554273264678095061 := by
  unfold tailWord_6086178
  simp only [CollatzResearch.WordTrace]
  refine ⟨55495287036206004323436797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147987432096549344862498125 55495287036206004323436797)
  ·
    refine ⟨20810732638577251621288799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55495287036206004323436797 20810732638577251621288799)
    ·
      refine ⟨31216098957865877431933199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20810732638577251621288799 31216098957865877431933199)
      ·
        refine ⟨46824148436798816147899799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31216098957865877431933199 46824148436798816147899799)
        ·
          refine ⟨70236222655198224221849699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46824148436798816147899799 70236222655198224221849699)
          ·
            refine ⟨105354333982797336332774549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70236222655198224221849699 105354333982797336332774549)
            ·
              refine ⟨4938484405443625140598807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 105354333982797336332774549 4938484405443625140598807)
              ·
                refine ⟨7407726608165437710898211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4938484405443625140598807 7407726608165437710898211)
                ·
                  refine ⟨11111589912248156566347317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7407726608165437710898211 11111589912248156566347317)
                  ·
                    refine ⟨1041711554273264678095061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11111589912248156566347317 1041711554273264678095061)
                    ·
                      rfl

theorem cell23_6086178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_6086178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086178 prefixEnd_6086178 := by exact prefixLift 6086178
  have htrace : WordTrace (prefixWord ++ tailWord_6086178) baseStart_6086178 baseEnd_6086178 := by
    simpa [prefixWord, tailWord_6086178, baseEnd_6086178] using wordTrace_append hprefix tailTrace_6086178
  have hstable : (prefixWord ++ tailWord_6086178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086178).length < 2 ^ (prefixWord ++ tailWord_6086178).sum := by decide
  have hdescent : baseEnd_6086178 < baseStart_6086178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086194 : List Nat := [3, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6]
def baseStart_6086194 : Nat := 118140960795 + 6086194 * 2 ^ 59
def prefixEnd_6086194 : Nat := 4983230072969 + 3 ^ 40 * 6086194 * 2
def baseEnd_6086194 : Nat := 3125142878510265971685109

theorem tailTrace_6086194 : CollatzResearch.WordTrace tailWord_6086194 prefixEnd_6086194 3125142878510265971685109 := by
  unfold tailWord_6086194
  simp only [CollatzResearch.WordTrace]
  refine ⟨55495432928191513006582409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147987821141844034684219757 55495432928191513006582409)
  ·
    refine ⟨41621574696143634754936807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55495432928191513006582409 41621574696143634754936807)
    ·
      refine ⟨62432362044215452132405211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41621574696143634754936807 62432362044215452132405211)
      ·
        refine ⟨93648543066323178198607817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62432362044215452132405211 93648543066323178198607817)
        ·
          refine ⟨70236407299742383648955863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93648543066323178198607817 70236407299742383648955863)
          ·
            refine ⟨105354610949613575473433795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70236407299742383648955863 105354610949613575473433795)
            ·
              refine ⟨158031916424420363210150693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105354610949613575473433795 158031916424420363210150693)
              ·
                refine ⟨29630984329578818101903255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158031916424420363210150693 29630984329578818101903255)
                ·
                  refine ⟨44446476494368227152854883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29630984329578818101903255 44446476494368227152854883)
                  ·
                    refine ⟨66669714741552340729282325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44446476494368227152854883 66669714741552340729282325)
                    ·
                      refine ⟨3125142878510265971685109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66669714741552340729282325 3125142878510265971685109)
                      ·
                        rfl

theorem cell23_6086194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_6086194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086194 prefixEnd_6086194 := by exact prefixLift 6086194
  have htrace : WordTrace (prefixWord ++ tailWord_6086194) baseStart_6086194 baseEnd_6086194 := by
    simpa [prefixWord, tailWord_6086194, baseEnd_6086194] using wordTrace_append hprefix tailTrace_6086194
  have hstable : (prefixWord ++ tailWord_6086194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086194).length < 2 ^ (prefixWord ++ tailWord_6086194).sum := by decide
  have hdescent : baseEnd_6086194 < baseStart_6086194 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086201 : List Nat := [1, 2, 1, 5, 1, 3, 1, 2, 1, 1, 5]
def baseStart_6086201 : Nat := 118140960795 + 6086201 * 2 ^ 59
def prefixEnd_6086201 : Nat := 4983230072969 + 3 ^ 40 * 6086201 * 2
def baseEnd_6086201 : Nat := 3125146472874847444297577

theorem tailTrace_6086201 : CollatzResearch.WordTrace tailWord_6086201 prefixEnd_6086201 3125146472874847444297577 := by
  unfold tailWord_6086201
  simp only [CollatzResearch.WordTrace]
  refine ⟨221981987023740692221834457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147987991349160461481222971 221981987023740692221834457)
  ·
    refine ⟨166486490267805519166375843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221981987023740692221834457 166486490267805519166375843)
    ·
      refine ⟨249729735401708278749563765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166486490267805519166375843 249729735401708278749563765)
      ·
        refine ⟨23412162693910151132771603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 249729735401708278749563765 23412162693910151132771603)
        ·
          refine ⟨35118244040865226699157405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23412162693910151132771603 35118244040865226699157405)
          ·
            refine ⟨13169341515324460012184027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35118244040865226699157405 13169341515324460012184027)
            ·
              refine ⟨19754012272986690018276041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13169341515324460012184027 19754012272986690018276041)
              ·
                refine ⟨14815509204740017513707031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19754012272986690018276041 14815509204740017513707031)
                ·
                  refine ⟨22223263807110026270560547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14815509204740017513707031 22223263807110026270560547)
                  ·
                    refine ⟨33334895710665039405840821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22223263807110026270560547 33334895710665039405840821)
                    ·
                      refine ⟨3125146472874847444297577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33334895710665039405840821 3125146472874847444297577)
                      ·
                        rfl

theorem cell23_6086201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_6086201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086201 prefixEnd_6086201 := by exact prefixLift 6086201
  have htrace : WordTrace (prefixWord ++ tailWord_6086201) baseStart_6086201 baseEnd_6086201 := by
    simpa [prefixWord, tailWord_6086201, baseEnd_6086201] using wordTrace_append hprefix tailTrace_6086201
  have hstable : (prefixWord ++ tailWord_6086201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086201).length < 2 ^ (prefixWord ++ tailWord_6086201).sum := by decide
  have hdescent : baseEnd_6086201 < baseStart_6086201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086218 : List Nat := [3, 1, 2, 1, 1, 3, 4, 2, 1, 2, 3]
def baseStart_6086218 : Nat := 118140960795 + 6086218 * 2 ^ 59
def prefixEnd_6086218 : Nat := 4983230072969 + 3 ^ 40 * 6086218 * 2
def baseEnd_6086218 : Nat := 3125155202045973877784999

theorem tailTrace_6086218 : CollatzResearch.WordTrace tailWord_6086218 prefixEnd_6086218 3125155202045973877784999 := by
  unfold tailWord_6086218
  simp only [CollatzResearch.WordTrace]
  refine ⟨55495651766169776031300827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147988404709786069416802205 55495651766169776031300827)
  ·
    refine ⟨83243477649254664046951241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55495651766169776031300827 83243477649254664046951241)
    ·
      refine ⟨62432608236940998035213431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83243477649254664046951241 62432608236940998035213431)
      ·
        refine ⟨93648912355411497052820147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62432608236940998035213431 93648912355411497052820147)
        ·
          refine ⟨140473368533117245579230221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93648912355411497052820147 140473368533117245579230221)
          ·
            refine ⟨52677513199918967092211333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140473368533117245579230221 52677513199918967092211333)
            ·
              refine ⟨9877033724984806329789625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52677513199918967092211333 9877033724984806329789625)
              ·
                refine ⟨7407775293738604747342219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9877033724984806329789625 7407775293738604747342219)
                ·
                  refine ⟨11111662940607907121013329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7407775293738604747342219 11111662940607907121013329)
                  ·
                    refine ⟨8333747205455930340759997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11111662940607907121013329 8333747205455930340759997)
                    ·
                      refine ⟨3125155202045973877784999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8333747205455930340759997 3125155202045973877784999)
                      ·
                        rfl

theorem cell23_6086218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 1, 2, 3].length) (baseStart_6086218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086218 prefixEnd_6086218 := by exact prefixLift 6086218
  have htrace : WordTrace (prefixWord ++ tailWord_6086218) baseStart_6086218 baseEnd_6086218 := by
    simpa [prefixWord, tailWord_6086218, baseEnd_6086218] using wordTrace_append hprefix tailTrace_6086218
  have hstable : (prefixWord ++ tailWord_6086218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086218).length < 2 ^ (prefixWord ++ tailWord_6086218).sum := by decide
  have hdescent : baseEnd_6086218 < baseStart_6086218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086288 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 6, 2, 2]
def baseStart_6086288 : Nat := 118140960795 + 6086288 * 2 ^ 59
def prefixEnd_6086288 : Nat := 4983230072969 + 3 ^ 40 * 6086288 * 2
def baseEnd_6086288 : Nat := 3125191145691788603909677

theorem tailTrace_6086288 : CollatzResearch.WordTrace tailWord_6086288 prefixEnd_6086288 3125191145691788603909677 := by
  unfold tailWord_6086288
  simp only [CollatzResearch.WordTrace]
  refine ⟨110992580087212753040125759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147990106782950337386834345 110992580087212753040125759)
  ·
    refine ⟨166488870130819129560188639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110992580087212753040125759 166488870130819129560188639)
    ·
      refine ⟨249733305196228694340282959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166488870130819129560188639 249733305196228694340282959)
      ·
        refine ⟨374599957794343041510424439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249733305196228694340282959 374599957794343041510424439)
        ·
          refine ⟨561899936691514562265636659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374599957794343041510424439 561899936691514562265636659)
          ·
            refine ⟨842849905037271843398454989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561899936691514562265636659 842849905037271843398454989)
            ·
              refine ⟨316068714388976941274420621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 842849905037271843398454989 316068714388976941274420621)
              ·
                refine ⟨118525767895866352977907733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 316068714388976941274420621 118525767895866352977907733)
                ·
                  refine ⟨5555895370118735295839425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 118525767895866352977907733 5555895370118735295839425)
                  ·
                    refine ⟨4166921527589051471879569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5555895370118735295839425 4166921527589051471879569)
                    ·
                      refine ⟨3125191145691788603909677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4166921527589051471879569 3125191145691788603909677)
                      ·
                        rfl

theorem cell23_6086288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 6, 2, 2].length) (baseStart_6086288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086288 prefixEnd_6086288 := by exact prefixLift 6086288
  have htrace : WordTrace (prefixWord ++ tailWord_6086288) baseStart_6086288 baseEnd_6086288 := by
    simpa [prefixWord, tailWord_6086288, baseEnd_6086288] using wordTrace_append hprefix tailTrace_6086288
  have hstable : (prefixWord ++ tailWord_6086288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086288).length < 2 ^ (prefixWord ++ tailWord_6086288).sum := by decide
  have hdescent : baseEnd_6086288 < baseStart_6086288 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086301 : List Nat := [1, 4, 2, 1, 1, 1, 1, 4, 2, 2, 4]
def baseStart_6086301 : Nat := 118140960795 + 6086301 * 2 ^ 59
def prefixEnd_6086301 : Nat := 4983230072969 + 3 ^ 40 * 6086301 * 2
def baseEnd_6086301 : Nat := 3125197820940297053047117

theorem tailTrace_6086301 : CollatzResearch.WordTrace tailWord_6086301 prefixEnd_6086301 3125197820940297053047117 := by
  unfold tailWord_6086301
  simp only [CollatzResearch.WordTrace]
  refine ⟨221985634323378409300474757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147990422882252272866983171 221985634323378409300474757)
  ·
    refine ⟨41622306435633451743839017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 221985634323378409300474757 41622306435633451743839017)
    ·
      refine ⟨31216729826725088807879263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41622306435633451743839017 31216729826725088807879263)
      ·
        refine ⟨46825094740087633211818895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31216729826725088807879263 46825094740087633211818895)
        ·
          refine ⟨70237642110131449817728343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46825094740087633211818895 70237642110131449817728343)
          ·
            refine ⟨105356463165197174726592515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70237642110131449817728343 105356463165197174726592515)
            ·
              refine ⟨158034694747795762089888773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105356463165197174726592515 158034694747795762089888773)
              ·
                refine ⟨29631505265211705391854145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158034694747795762089888773 29631505265211705391854145)
                ·
                  refine ⟨22223628948908779043890609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29631505265211705391854145 22223628948908779043890609)
                  ·
                    refine ⟨16667721711681584282917957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22223628948908779043890609 16667721711681584282917957)
                    ·
                      refine ⟨3125197820940297053047117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16667721711681584282917957 3125197820940297053047117)
                      ·
                        rfl

theorem cell23_6086301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_6086301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086301 prefixEnd_6086301 := by exact prefixLift 6086301
  have htrace : WordTrace (prefixWord ++ tailWord_6086301) baseStart_6086301 baseEnd_6086301 := by
    simpa [prefixWord, tailWord_6086301, baseEnd_6086301] using wordTrace_append hprefix tailTrace_6086301
  have hstable : (prefixWord ++ tailWord_6086301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086301).length < 2 ^ (prefixWord ++ tailWord_6086301).sum := by decide
  have hdescent : baseEnd_6086301 < baseStart_6086301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086401 : List Nat := [1, 2, 4, 1, 1, 1, 3, 2, 8]
def baseStart_6086401 : Nat := 118140960795 + 6086401 * 2 ^ 59
def prefixEnd_6086401 : Nat := 4983230072969 + 3 ^ 40 * 6086401 * 2
def baseEnd_6086401 : Nat := 347249907667305184644073

theorem tailTrace_6086401 : CollatzResearch.WordTrace tailWord_6086401 prefixEnd_6086401 347249907667305184644073 := by
  unfold tailWord_6086401
  simp only [CollatzResearch.WordTrace]
  refine ⟨221989281623016126379115057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147992854415344084252743371 221989281623016126379115057)
  ·
    refine ⟨166491961217262094784336293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221989281623016126379115057 166491961217262094784336293)
    ·
      refine ⟨31217242728236642772063055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166491961217262094784336293 31217242728236642772063055)
      ·
        refine ⟨46825864092354964158094583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31217242728236642772063055 46825864092354964158094583)
        ·
          refine ⟨70238796138532446237141875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46825864092354964158094583 70238796138532446237141875)
          ·
            refine ⟨105358194207798669355712813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70238796138532446237141875 105358194207798669355712813)
            ·
              refine ⟨39509322827924501008392305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105358194207798669355712813 39509322827924501008392305)
              ·
                refine ⟨29631992120943375756294229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39509322827924501008392305 29631992120943375756294229)
                ·
                  refine ⟨347249907667305184644073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29631992120943375756294229 347249907667305184644073)
                  ·
                    rfl

theorem cell23_6086401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 8].length) (baseStart_6086401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086401 prefixEnd_6086401 := by exact prefixLift 6086401
  have htrace : WordTrace (prefixWord ++ tailWord_6086401) baseStart_6086401 baseEnd_6086401 := by
    simpa [prefixWord, tailWord_6086401, baseEnd_6086401] using wordTrace_append hprefix tailTrace_6086401
  have hstable : (prefixWord ++ tailWord_6086401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086401).length < 2 ^ (prefixWord ++ tailWord_6086401).sum := by decide
  have hdescent : baseEnd_6086401 < baseStart_6086401 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086413 : List Nat := [1, 7, 2, 1, 1, 1, 3, 2, 5]
def baseStart_6086413 : Nat := 118140960795 + 6086413 * 2 ^ 59
def prefixEnd_6086413 : Nat := 4983230072969 + 3 ^ 40 * 6086413 * 2
def baseEnd_6086413 : Nat := 347250592308177846094067

theorem tailTrace_6086413 : CollatzResearch.WordTrace tailWord_6086413 prefixEnd_6086413 347250592308177846094067 := by
  unfold tailWord_6086413
  simp only [CollatzResearch.WordTrace]
  refine ⟨221989719298972652428551893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147993146199315101619034595 221989719298972652428551893)
  ·
    refine ⟨5202884046069671541294185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 221989719298972652428551893 5202884046069671541294185)
    ·
      refine ⟨3902163034552253655970639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5202884046069671541294185 3902163034552253655970639)
      ·
        refine ⟨5853244551828380483955959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3902163034552253655970639 5853244551828380483955959)
        ·
          refine ⟨8779866827742570725933939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5853244551828380483955959 8779866827742570725933939)
          ·
            refine ⟨13169800241613856088900909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8779866827742570725933939 13169800241613856088900909)
            ·
              refine ⟨4938675090605196033337841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13169800241613856088900909 4938675090605196033337841)
              ·
                refine ⟨3704006317953897025003381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4938675090605196033337841 3704006317953897025003381)
                ·
                  refine ⟨347250592308177846094067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3704006317953897025003381 347250592308177846094067)
                  ·
                    rfl

theorem cell23_6086413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_6086413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086413 prefixEnd_6086413 := by exact prefixLift 6086413
  have htrace : WordTrace (prefixWord ++ tailWord_6086413) baseStart_6086413 baseEnd_6086413 := by
    simpa [prefixWord, tailWord_6086413, baseEnd_6086413] using wordTrace_append hprefix tailTrace_6086413
  have hstable : (prefixWord ++ tailWord_6086413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086413).length < 2 ^ (prefixWord ++ tailWord_6086413).sum := by decide
  have hdescent : baseEnd_6086413 < baseStart_6086413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086495 : List Nat := [1, 1, 2, 3, 1, 4, 2, 3, 2, 4]
def baseStart_6086495 : Nat := 118140960795 + 6086495 * 2 ^ 59
def prefixEnd_6086495 : Nat := 4983230072969 + 3 ^ 40 * 6086495 * 2
def baseEnd_6086495 : Nat := 1041765812062423098007075

theorem tailTrace_6086495 : CollatzResearch.WordTrace tailWord_6086495 prefixEnd_6086495 1041765812062423098007075 := by
  unfold tailWord_6086495
  simp only [CollatzResearch.WordTrace]
  refine ⟨221992710084675580433036939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147995140056450386955357959 221992710084675580433036939)
  ·
    refine ⟨332989065127013370649555409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221992710084675580433036939 332989065127013370649555409)
    ·
      refine ⟨249741798845260027987166557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332989065127013370649555409 249741798845260027987166557)
      ·
        refine ⟨93653174566972510495187459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249741798845260027987166557 93653174566972510495187459)
        ·
          refine ⟨140479761850458765742781189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93653174566972510495187459 140479761850458765742781189)
          ·
            refine ⟨26339955346961018576771473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140479761850458765742781189 26339955346961018576771473)
            ·
              refine ⟨19754966510220763932578605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26339955346961018576771473 19754966510220763932578605)
              ·
                refine ⟨7408112441332786474716977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19754966510220763932578605 7408112441332786474716977)
                ·
                  refine ⟨5556084330999589856037733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7408112441332786474716977 5556084330999589856037733)
                  ·
                    refine ⟨1041765812062423098007075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5556084330999589856037733 1041765812062423098007075)
                    ·
                      rfl

theorem cell23_6086495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 2, 4].length) (baseStart_6086495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086495 prefixEnd_6086495 := by exact prefixLift 6086495
  have htrace : WordTrace (prefixWord ++ tailWord_6086495) baseStart_6086495 baseEnd_6086495 := by
    simpa [prefixWord, tailWord_6086495, baseEnd_6086495] using wordTrace_append hprefix tailTrace_6086495
  have hstable : (prefixWord ++ tailWord_6086495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086495).length < 2 ^ (prefixWord ++ tailWord_6086495).sum := by decide
  have hdescent : baseEnd_6086495 < baseStart_6086495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086506 : List Nat := [3, 1, 3, 4, 1, 2, 1, 1, 2, 3, 2]
def baseStart_6086506 : Nat := 118140960795 + 6086506 * 2 ^ 59
def prefixEnd_6086506 : Nat := 4983230072969 + 3 ^ 40 * 6086506 * 2
def baseEnd_6086506 : Nat := 3125303084474468750983675

theorem tailTrace_6086506 : CollatzResearch.WordTrace tailWord_6086506 prefixEnd_6086506 3125303084474468750983675 := by
  unfold tailWord_6086506
  simp only [CollatzResearch.WordTrace]
  refine ⟨55498277821908932327921843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147995407525090486207791581 55498277821908932327921843)
  ·
    refine ⟨83247416732863398491882765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55498277821908932327921843 83247416732863398491882765)
    ·
      refine ⟨31217781274823774434456037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83247416732863398491882765 31217781274823774434456037)
      ·
        refine ⟨5853333989029457706460507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31217781274823774434456037 5853333989029457706460507)
        ·
          refine ⟨8780000983544186559690761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5853333989029457706460507 8780000983544186559690761)
          ·
            refine ⟨6585000737658139919768071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8780000983544186559690761 6585000737658139919768071)
            ·
              refine ⟨9877501106487209879652107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6585000737658139919768071 9877501106487209879652107)
              ·
                refine ⟨14816251659730814819478161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9877501106487209879652107 14816251659730814819478161)
                ·
                  refine ⟨11112188744798111114608621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14816251659730814819478161 11112188744798111114608621)
                  ·
                    refine ⟨4167070779299291667978233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11112188744798111114608621 4167070779299291667978233)
                    ·
                      refine ⟨3125303084474468750983675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4167070779299291667978233 3125303084474468750983675)
                      ·
                        rfl

theorem cell23_6086506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_6086506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086506 prefixEnd_6086506 := by exact prefixLift 6086506
  have htrace : WordTrace (prefixWord ++ tailWord_6086506) baseStart_6086506 baseEnd_6086506 := by
    simpa [prefixWord, tailWord_6086506, baseEnd_6086506] using wordTrace_append hprefix tailTrace_6086506
  have hstable : (prefixWord ++ tailWord_6086506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086506).length < 2 ^ (prefixWord ++ tailWord_6086506).sum := by decide
  have hdescent : baseEnd_6086506 < baseStart_6086506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086522 : List Nat := [3, 1, 1, 1, 1, 1, 8, 1, 1, 2, 3]
def baseStart_6086522 : Nat := 118140960795 + 6086522 * 2 ^ 59
def prefixEnd_6086522 : Nat := 4983230072969 + 3 ^ 40 * 6086522 * 2
def baseEnd_6086522 : Nat := 3125311300164940688383601

theorem tailTrace_6086522 : CollatzResearch.WordTrace tailWord_6086522 prefixEnd_6086522 3125311300164940688383601 := by
  unfold tailWord_6086522
  simp only [CollatzResearch.WordTrace]
  refine ⟨55498423713894441011067455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147995796570385176029513213 55498423713894441011067455)
  ·
    refine ⟨83247635570841661516601183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55498423713894441011067455 83247635570841661516601183)
    ·
      refine ⟨124871453356262492274901775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83247635570841661516601183 124871453356262492274901775)
      ·
        refine ⟨187307180034393738412352663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124871453356262492274901775 187307180034393738412352663)
        ·
          refine ⟨280960770051590607618528995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187307180034393738412352663 280960770051590607618528995)
          ·
            refine ⟨421441155077385911427793493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280960770051590607618528995 421441155077385911427793493)
            ·
              refine ⟨4938763536063116149544455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 421441155077385911427793493 4938763536063116149544455)
              ·
                refine ⟨7408145304094674224316683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4938763536063116149544455 7408145304094674224316683)
                ·
                  refine ⟨11112217956142011336475025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7408145304094674224316683 11112217956142011336475025)
                  ·
                    refine ⟨8334163467106508502356269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11112217956142011336475025 8334163467106508502356269)
                    ·
                      refine ⟨3125311300164940688383601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8334163467106508502356269 3125311300164940688383601)
                      ·
                        rfl

theorem cell23_6086522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 1, 2, 3].length) (baseStart_6086522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086522 prefixEnd_6086522 := by exact prefixLift 6086522
  have htrace : WordTrace (prefixWord ++ tailWord_6086522) baseStart_6086522 baseEnd_6086522 := by
    simpa [prefixWord, tailWord_6086522, baseEnd_6086522] using wordTrace_append hprefix tailTrace_6086522
  have hstable : (prefixWord ++ tailWord_6086522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086522).length < 2 ^ (prefixWord ++ tailWord_6086522).sum := by decide
  have hdescent : baseEnd_6086522 < baseStart_6086522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086545 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 5, 3, 2]
def baseStart_6086545 : Nat := 118140960795 + 6086545 * 2 ^ 59
def prefixEnd_6086545 : Nat := 4983230072969 + 3 ^ 40 * 6086545 * 2
def baseEnd_6086545 : Nat := 3125323110219994098395995

theorem tailTrace_6086545 : CollatzResearch.WordTrace tailWord_6086545 prefixEnd_6086545 3125323110219994098395995 := by
  unfold tailWord_6086545
  simp only [CollatzResearch.WordTrace]
  refine ⟨221994533734494438972357089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147996355822996292648238059 221994533734494438972357089)
  ·
    refine ⟨166495900300870829229267817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221994533734494438972357089 166495900300870829229267817)
    ·
      refine ⟨124871925225653121921950863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166495900300870829229267817 124871925225653121921950863)
      ·
        refine ⟨187307887838479682882926295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124871925225653121921950863 187307887838479682882926295)
        ·
          refine ⟨280961831757719524324389443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187307887838479682882926295 280961831757719524324389443)
          ·
            refine ⟨421442747636579286486584165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280961831757719524324389443 421442747636579286486584165)
            ·
              refine ⟨79020515181858616216234531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 421442747636579286486584165 79020515181858616216234531)
              ·
                refine ⟨118530772772787924324351797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79020515181858616216234531 118530772772787924324351797)
                ·
                  refine ⟨11112259947448867905407981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 118530772772787924324351797 11112259947448867905407981)
                  ·
                    refine ⟨4167097480293325464527993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11112259947448867905407981 4167097480293325464527993)
                    ·
                      refine ⟨3125323110219994098395995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4167097480293325464527993 3125323110219994098395995)
                      ·
                        rfl

theorem cell23_6086545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 3, 2].length) (baseStart_6086545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086545 prefixEnd_6086545 := by exact prefixLift 6086545
  have htrace : WordTrace (prefixWord ++ tailWord_6086545) baseStart_6086545 baseEnd_6086545 := by
    simpa [prefixWord, tailWord_6086545, baseEnd_6086545] using wordTrace_append hprefix tailTrace_6086545
  have hstable : (prefixWord ++ tailWord_6086545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086545).length < 2 ^ (prefixWord ++ tailWord_6086545).sum := by decide
  have hdescent : baseEnd_6086545 < baseStart_6086545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086575 : List Nat := [1, 1, 2, 1, 2, 2, 4, 1, 3, 4, 2]
def baseStart_6086575 : Nat := 118140960795 + 6086575 * 2 ^ 59
def prefixEnd_6086575 : Nat := 4983230072969 + 3 ^ 40 * 6086575 * 2
def baseEnd_6086575 : Nat := 3125338514639628981020857

theorem tailTrace_6086575 : CollatzResearch.WordTrace tailWord_6086575 prefixEnd_6086575 3125338514639628981020857 := by
  unfold tailWord_6086575
  simp only [CollatzResearch.WordTrace]
  refine ⟨221995627924385754095949179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147997085282923836063966119 221995627924385754095949179)
  ·
    refine ⟨332993441886578631143923769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221995627924385754095949179 332993441886578631143923769)
    ·
      refine ⟨249745081414933973357942827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332993441886578631143923769 249745081414933973357942827)
      ·
        refine ⟨374617622122400960036914241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249745081414933973357942827 374617622122400960036914241)
        ·
          refine ⟨280963216591800720027685681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374617622122400960036914241 280963216591800720027685681)
          ·
            refine ⟨210722412443850540020764261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280963216591800720027685681 210722412443850540020764261)
            ·
              refine ⟨39510452333221976253893299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 210722412443850540020764261 39510452333221976253893299)
              ·
                refine ⟨59265678499832964380839949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39510452333221976253893299 59265678499832964380839949)
                ·
                  refine ⟨22224629437437361642814981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59265678499832964380839949 22224629437437361642814981)
                  ·
                    refine ⟨4167118019519505308027809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22224629437437361642814981 4167118019519505308027809)
                    ·
                      refine ⟨3125338514639628981020857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4167118019519505308027809 3125338514639628981020857)
                      ·
                        rfl

theorem cell23_6086575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 4, 2].length) (baseStart_6086575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086575 prefixEnd_6086575 := by exact prefixLift 6086575
  have htrace : WordTrace (prefixWord ++ tailWord_6086575) baseStart_6086575 baseEnd_6086575 := by
    simpa [prefixWord, tailWord_6086575, baseEnd_6086575] using wordTrace_append hprefix tailTrace_6086575
  have hstable : (prefixWord ++ tailWord_6086575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086575).length < 2 ^ (prefixWord ++ tailWord_6086575).sum := by decide
  have hdescent : baseEnd_6086575 < baseStart_6086575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086592 : List Nat := [2, 1, 1, 2, 3, 2, 1, 3, 4, 2, 2]
def baseStart_6086592 : Nat := 118140960795 + 6086592 * 2 ^ 59
def prefixEnd_6086592 : Nat := 4983230072969 + 3 ^ 40 * 6086592 * 2
def baseEnd_6086592 : Nat := 3125347243810755414508279

theorem tailTrace_6086592 : CollatzResearch.WordTrace tailWord_6086592 prefixEnd_6086592 3125347243810755414508279 := by
  unfold tailWord_6086592
  simp only [CollatzResearch.WordTrace]
  refine ⟨110998123982662082999659015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 147997498643549443999545353 110998123982662082999659015)
  ·
    refine ⟨166497185973993124499488523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110998123982662082999659015 166497185973993124499488523)
    ·
      refine ⟨249745778960989686749232785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166497185973993124499488523 249745778960989686749232785)
      ·
        refine ⟨187309334220742265061924589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249745778960989686749232785 187309334220742265061924589)
        ·
          refine ⟨70241000332778349398221721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187309334220742265061924589 70241000332778349398221721)
          ·
            refine ⟨52680750249583762048666291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70241000332778349398221721 52680750249583762048666291)
            ·
              refine ⟨79021125374375643072999437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52680750249583762048666291 79021125374375643072999437)
              ·
                refine ⟨29632922015390866152374789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79021125374375643072999437 29632922015390866152374789)
                ·
                  refine ⟨5556172877885787403570273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29632922015390866152374789 5556172877885787403570273)
                  ·
                    refine ⟨4167129658414340552677705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5556172877885787403570273 4167129658414340552677705)
                    ·
                      refine ⟨3125347243810755414508279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4167129658414340552677705 3125347243810755414508279)
                      ·
                        rfl

theorem cell23_6086592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3, 4, 2, 2].length) (baseStart_6086592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086592 prefixEnd_6086592 := by exact prefixLift 6086592
  have htrace : WordTrace (prefixWord ++ tailWord_6086592) baseStart_6086592 baseEnd_6086592 := by
    simpa [prefixWord, tailWord_6086592, baseEnd_6086592] using wordTrace_append hprefix tailTrace_6086592
  have hstable : (prefixWord ++ tailWord_6086592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086592).length < 2 ^ (prefixWord ++ tailWord_6086592).sum := by decide
  have hdescent : baseEnd_6086592 < baseStart_6086592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086626 : List Nat := [3, 3, 3, 1, 2, 1, 1, 2, 1, 4, 2]
def baseStart_6086626 : Nat := 118140960795 + 6086626 * 2 ^ 59
def prefixEnd_6086626 : Nat := 4983230072969 + 3 ^ 40 * 6086626 * 2
def baseEnd_6086626 : Nat := 3125364702153008281483123

theorem tailTrace_6086626 : CollatzResearch.WordTrace tailWord_6086626 prefixEnd_6086626 3125364702153008281483123 := by
  unfold tailWord_6086626
  simp only [CollatzResearch.WordTrace]
  refine ⟨55499372011800247451513933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147998325364800659870703821 55499372011800247451513933)
  ·
    refine ⟨20812264504425092794317725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55499372011800247451513933 20812264504425092794317725)
    ·
      refine ⟨7804599189159409797869147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20812264504425092794317725 7804599189159409797869147)
      ·
        refine ⟨11706898783739114696803721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7804599189159409797869147 11706898783739114696803721)
        ·
          refine ⟨8780174087804336022602791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11706898783739114696803721 8780174087804336022602791)
          ·
            refine ⟨13170261131706504033904187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8780174087804336022602791 13170261131706504033904187)
            ·
              refine ⟨19755391697559756050856281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13170261131706504033904187 19755391697559756050856281)
              ·
                refine ⟨14816543773169817038142211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19755391697559756050856281 14816543773169817038142211)
                ·
                  refine ⟨22224815659754725557213317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14816543773169817038142211 22224815659754725557213317)
                  ·
                    refine ⟨4167152936204011041977497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22224815659754725557213317 4167152936204011041977497)
                    ·
                      refine ⟨3125364702153008281483123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4167152936204011041977497 3125364702153008281483123)
                      ·
                        rfl

theorem cell23_6086626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_6086626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086626 prefixEnd_6086626 := by exact prefixLift 6086626
  have htrace : WordTrace (prefixWord ++ tailWord_6086626) baseStart_6086626 baseEnd_6086626 := by
    simpa [prefixWord, tailWord_6086626, baseEnd_6086626] using wordTrace_append hprefix tailTrace_6086626
  have hstable : (prefixWord ++ tailWord_6086626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086626).length < 2 ^ (prefixWord ++ tailWord_6086626).sum := by decide
  have hdescent : baseEnd_6086626 < baseStart_6086626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086635 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 4, 5, 2]
def baseStart_6086635 : Nat := 118140960795 + 6086635 * 2 ^ 59
def prefixEnd_6086635 : Nat := 4983230072969 + 3 ^ 40 * 6086635 * 2
def baseEnd_6086635 : Nat := 3125369323478898746270581

theorem tailTrace_6086635 : CollatzResearch.WordTrace tailWord_6086635 prefixEnd_6086635 3125369323478898746270581 := by
  unfold tailWord_6086635
  simp only [CollatzResearch.WordTrace]
  refine ⟨221997816304168384343133359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147998544202778922895422239 221997816304168384343133359)
  ·
    refine ⟨332996724456252576514700039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221997816304168384343133359 332996724456252576514700039)
    ·
      refine ⟨499495086684378864772050059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332996724456252576514700039 499495086684378864772050059)
      ·
        refine ⟨749242630026568297158075089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 499495086684378864772050059 749242630026568297158075089)
        ·
          refine ⟨561931972519926222868556317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 749242630026568297158075089 561931972519926222868556317)
          ·
            refine ⟨210724489694972333575708619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 561931972519926222868556317 210724489694972333575708619)
            ·
              refine ⟨316086734542458500363562929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210724489694972333575708619 316086734542458500363562929)
              ·
                refine ⟨237065050906843875272672197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 316086734542458500363562929 237065050906843875272672197)
                ·
                  refine ⟨44449697045033226613626037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 237065050906843875272672197 44449697045033226613626037)
                  ·
                    refine ⟨4167159097971864995027441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44449697045033226613626037 4167159097971864995027441)
                    ·
                      refine ⟨3125369323478898746270581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4167159097971864995027441 3125369323478898746270581)
                      ·
                        rfl

theorem cell23_6086635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 5, 2].length) (baseStart_6086635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086635 prefixEnd_6086635 := by exact prefixLift 6086635
  have htrace : WordTrace (prefixWord ++ tailWord_6086635) baseStart_6086635 baseEnd_6086635 := by
    simpa [prefixWord, tailWord_6086635, baseEnd_6086635] using wordTrace_append hprefix tailTrace_6086635
  have hstable : (prefixWord ++ tailWord_6086635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086635).length < 2 ^ (prefixWord ++ tailWord_6086635).sum := by decide
  have hdescent : baseEnd_6086635 < baseStart_6086635 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086649 : List Nat := [1, 2, 1, 3, 1, 6, 2, 2, 5]
def baseStart_6086649 : Nat := 118140960795 + 6086649 * 2 ^ 59
def prefixEnd_6086649 : Nat := 4983230072969 + 3 ^ 40 * 6086649 * 2
def baseEnd_6086649 : Nat := 347264056912006854610613

theorem tailTrace_6086649 : CollatzResearch.WordTrace tailWord_6086649 prefixEnd_6086649 347264056912006854610613 := by
  unfold tailWord_6086649
  simp only [CollatzResearch.WordTrace]
  refine ⟨221998326926117664734143001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147998884617411776489428667 221998326926117664734143001)
  ·
    refine ⟨166498745194588248550607251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 221998326926117664734143001 166498745194588248550607251)
    ·
      refine ⟨249748117791882372825910877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166498745194588248550607251 249748117791882372825910877)
      ·
        refine ⟨93655544171955889809716579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249748117791882372825910877 93655544171955889809716579)
        ·
          refine ⟨140483316257933834714574869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93655544171955889809716579 140483316257933834714574869)
          ·
            refine ⟨6585155449590648502245697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 140483316257933834714574869 6585155449590648502245697)
            ·
              refine ⟨4938866587192986376684273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6585155449590648502245697 4938866587192986376684273)
              ·
                refine ⟨3704149940394739782513205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4938866587192986376684273 3704149940394739782513205)
                ·
                  refine ⟨347264056912006854610613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3704149940394739782513205 347264056912006854610613)
                  ·
                    rfl

theorem cell23_6086649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 2, 5].length) (baseStart_6086649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086649 prefixEnd_6086649 := by exact prefixLift 6086649
  have htrace : WordTrace (prefixWord ++ tailWord_6086649) baseStart_6086649 baseEnd_6086649 := by
    simpa [prefixWord, tailWord_6086649, baseEnd_6086649] using wordTrace_append hprefix tailTrace_6086649
  have hstable : (prefixWord ++ tailWord_6086649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086649).length < 2 ^ (prefixWord ++ tailWord_6086649).sum := by decide
  have hdescent : baseEnd_6086649 < baseStart_6086649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086675 : List Nat := [1, 1, 1, 2, 1, 4, 3, 1, 5, 4]
def baseStart_6086675 : Nat := 118140960795 + 6086675 * 2 ^ 59
def prefixEnd_6086675 : Nat := 4983230072969 + 3 ^ 40 * 6086675 * 2
def baseEnd_6086675 : Nat := 1041796620901692863256799

theorem tailTrace_6086675 : CollatzResearch.WordTrace tailWord_6086675 prefixEnd_6086675 1041796620901692863256799 := by
  unfold tailWord_6086675
  simp only [CollatzResearch.WordTrace]
  refine ⟨221999275224023471174589479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147999516816015647449726319 221999275224023471174589479)
  ·
    refine ⟨332998912836035206761884219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221999275224023471174589479 332998912836035206761884219)
    ·
      refine ⟨499498369254052810142826329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332998912836035206761884219 499498369254052810142826329)
      ·
        refine ⟨374623776940539607607119747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 499498369254052810142826329 374623776940539607607119747)
        ·
          refine ⟨561935665410809411410679621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374623776940539607607119747 561935665410809411410679621)
          ·
            refine ⟨105362937264526764639502429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 561935665410809411410679621 105362937264526764639502429)
            ·
              refine ⟨39511101474197536739813411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105362937264526764639502429 39511101474197536739813411)
              ·
                refine ⟨59266652211296305109720117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39511101474197536739813411 59266652211296305109720117)
                ·
                  refine ⟨5556248644809028604036261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59266652211296305109720117 5556248644809028604036261)
                  ·
                    refine ⟨1041796620901692863256799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5556248644809028604036261 1041796620901692863256799)
                    ·
                      rfl

theorem cell23_6086675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 5, 4].length) (baseStart_6086675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086675 prefixEnd_6086675 := by exact prefixLift 6086675
  have htrace : WordTrace (prefixWord ++ tailWord_6086675) baseStart_6086675 baseEnd_6086675 := by
    simpa [prefixWord, tailWord_6086675, baseEnd_6086675] using wordTrace_append hprefix tailTrace_6086675
  have hstable : (prefixWord ++ tailWord_6086675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086675).length < 2 ^ (prefixWord ++ tailWord_6086675).sum := by decide
  have hdescent : baseEnd_6086675 < baseStart_6086675 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086679 : List Nat := [1, 1, 3, 5, 2, 2, 1, 1, 2, 5]
def baseStart_6086679 : Nat := 118140960795 + 6086679 * 2 ^ 59
def prefixEnd_6086679 : Nat := 4983230072969 + 3 ^ 40 * 6086679 * 2
def baseEnd_6086679 : Nat := 1041797305542565524706793

theorem tailTrace_6086679 : CollatzResearch.WordTrace tailWord_6086679 prefixEnd_6086679 1041797305542565524706793 := by
  unfold tailWord_6086679
  simp only [CollatzResearch.WordTrace]
  refine ⟨221999421116008979857735091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 147999614077339319905156727 221999421116008979857735091)
  ·
    refine ⟨332999131674013469786602637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221999421116008979857735091 332999131674013469786602637)
    ·
      refine ⟨124874674377755051169975989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 332999131674013469786602637 124874674377755051169975989)
      ·
        refine ⟨11707000722914536047185249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 124874674377755051169975989 11707000722914536047185249)
        ·
          refine ⟨8780250542185902035388937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11707000722914536047185249 8780250542185902035388937)
          ·
            refine ⟨6585187906639426526541703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8780250542185902035388937 6585187906639426526541703)
            ·
              refine ⟨9877781859959139789812555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6585187906639426526541703 9877781859959139789812555)
              ·
                refine ⟨14816672789938709684718833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9877781859959139789812555 14816672789938709684718833)
                ·
                  refine ⟨11112504592454032263539125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14816672789938709684718833 11112504592454032263539125)
                  ·
                    refine ⟨1041797305542565524706793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11112504592454032263539125 1041797305542565524706793)
                    ·
                      rfl

theorem cell23_6086679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 5].length) (baseStart_6086679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086679 prefixEnd_6086679 := by exact prefixLift 6086679
  have htrace : WordTrace (prefixWord ++ tailWord_6086679) baseStart_6086679 baseEnd_6086679 := by
    simpa [prefixWord, tailWord_6086679, baseEnd_6086679] using wordTrace_append hprefix tailTrace_6086679
  have hstable : (prefixWord ++ tailWord_6086679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086679).length < 2 ^ (prefixWord ++ tailWord_6086679).sum := by decide
  have hdescent : baseEnd_6086679 < baseStart_6086679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086682 : List Nat := [3, 1, 1, 3, 1, 3, 3, 1, 2, 1, 4]
def baseStart_6086682 : Nat := 118140960795 + 6086682 * 2 ^ 59
def prefixEnd_6086682 : Nat := 4983230072969 + 3 ^ 40 * 6086682 * 2
def baseEnd_6086682 : Nat := 3125393457069660062382865

theorem tailTrace_6086682 : CollatzResearch.WordTrace tailWord_6086682 prefixEnd_6086682 3125393457069660062382865 := by
  unfold tailWord_6086682
  simp only [CollatzResearch.WordTrace]
  refine ⟨55499882633749527842523575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 147999687023332074246729533 55499882633749527842523575)
  ·
    refine ⟨83249823950624291763785363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55499882633749527842523575 83249823950624291763785363)
    ·
      refine ⟨124874735925936437645678045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83249823950624291763785363 124874735925936437645678045)
      ·
        refine ⟨46828025972226164117129267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124874735925936437645678045 46828025972226164117129267)
        ·
          refine ⟨70242038958339246175693901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46828025972226164117129267 70242038958339246175693901)
          ·
            refine ⟨26340764609377217315885213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70242038958339246175693901 26340764609377217315885213)
            ·
              refine ⟨9877786728516456493456955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26340764609377217315885213 9877786728516456493456955)
              ·
                refine ⟨14816680092774684740185433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9877786728516456493456955 14816680092774684740185433)
                ·
                  refine ⟨11112510069581013555139075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14816680092774684740185433 11112510069581013555139075)
                  ·
                    refine ⟨16668765104371520332708613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11112510069581013555139075 16668765104371520332708613)
                    ·
                      refine ⟨3125393457069660062382865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16668765104371520332708613 3125393457069660062382865)
                      ·
                        rfl

theorem cell23_6086682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_6086682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086682 prefixEnd_6086682 := by exact prefixLift 6086682
  have htrace : WordTrace (prefixWord ++ tailWord_6086682) baseStart_6086682 baseEnd_6086682 := by
    simpa [prefixWord, tailWord_6086682, baseEnd_6086682] using wordTrace_append hprefix tailTrace_6086682
  have hstable : (prefixWord ++ tailWord_6086682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086682).length < 2 ^ (prefixWord ++ tailWord_6086682).sum := by decide
  have hdescent : baseEnd_6086682 < baseStart_6086682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086705 : List Nat := [1, 2, 2, 3, 1, 4, 1, 1, 8]
def baseStart_6086705 : Nat := 118140960795 + 6086705 * 2 ^ 59
def prefixEnd_6086705 : Nat := 4983230072969 + 3 ^ 40 * 6086705 * 2
def baseEnd_6086705 : Nat := 347267251902745941377251

theorem tailTrace_6086705 : CollatzResearch.WordTrace tailWord_6086705 prefixEnd_6086705 347267251902745941377251 := by
  unfold tailWord_6086705
  simp only [CollatzResearch.WordTrace]
  refine ⟨222000369413914786298181569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148000246275943190865454379 222000369413914786298181569)
  ·
    refine ⟨166500277060436089723636177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222000369413914786298181569 166500277060436089723636177)
    ·
      refine ⟨124875207795327067292727133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166500277060436089723636177 124875207795327067292727133)
      ·
        refine ⟨46828202923247650234772675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124875207795327067292727133 46828202923247650234772675)
        ·
          refine ⟨70242304384871475352159013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46828202923247650234772675 70242304384871475352159013)
          ·
            refine ⟨13170432072163401628529815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70242304384871475352159013 13170432072163401628529815)
            ·
              refine ⟨19755648108245102442794723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13170432072163401628529815 19755648108245102442794723)
              ·
                refine ⟨29633472162367653664192085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19755648108245102442794723 29633472162367653664192085)
                ·
                  refine ⟨347267251902745941377251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29633472162367653664192085 347267251902745941377251)
                  ·
                    rfl

theorem cell23_6086705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 8].length) (baseStart_6086705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086705 prefixEnd_6086705 := by exact prefixLift 6086705
  have htrace : WordTrace (prefixWord ++ tailWord_6086705) baseStart_6086705 baseEnd_6086705 := by
    simpa [prefixWord, tailWord_6086705, baseEnd_6086705] using wordTrace_append hprefix tailTrace_6086705
  have hstable : (prefixWord ++ tailWord_6086705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086705).length < 2 ^ (prefixWord ++ tailWord_6086705).sum := by decide
  have hdescent : baseEnd_6086705 < baseStart_6086705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086709 : List Nat := [1, 3, 3, 1, 1, 1, 4, 4, 1, 4]
def baseStart_6086709 : Nat := 118140960795 + 6086709 * 2 ^ 59
def prefixEnd_6086709 : Nat := 4983230072969 + 3 ^ 40 * 6086709 * 2
def baseEnd_6086709 : Nat := 1041802440349110485581747

theorem tailTrace_6086709 : CollatzResearch.WordTrace tailWord_6086709 prefixEnd_6086709 1041802440349110485581747 := by
  unfold tailWord_6086709
  simp only [CollatzResearch.WordTrace]
  refine ⟨222000515305900294981327181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148000343537266863320884787 222000515305900294981327181)
  ·
    refine ⟨83250193239712610617997693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222000515305900294981327181 83250193239712610617997693)
    ·
      refine ⟨31218822464892228981749135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83250193239712610617997693 31218822464892228981749135)
      ·
        refine ⟨46828233697338343472623703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31218822464892228981749135 46828233697338343472623703)
        ·
          refine ⟨70242350546007515208935555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46828233697338343472623703 70242350546007515208935555)
          ·
            refine ⟨105363525819011272813403333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70242350546007515208935555 105363525819011272813403333)
            ·
              refine ⟨19755661091064613652513125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105363525819011272813403333 19755661091064613652513125)
              ·
                refine ⟨3704186454574615059846211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19755661091064613652513125 3704186454574615059846211)
                ·
                  refine ⟨5556279681861922589769317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3704186454574615059846211 5556279681861922589769317)
                  ·
                    refine ⟨1041802440349110485581747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5556279681861922589769317 1041802440349110485581747)
                    ·
                      rfl

theorem cell23_6086709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_6086709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086709 prefixEnd_6086709 := by exact prefixLift 6086709
  have htrace : WordTrace (prefixWord ++ tailWord_6086709) baseStart_6086709 baseEnd_6086709 := by
    simpa [prefixWord, tailWord_6086709, baseEnd_6086709] using wordTrace_append hprefix tailTrace_6086709
  have hstable : (prefixWord ++ tailWord_6086709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086709).length < 2 ^ (prefixWord ++ tailWord_6086709).sum := by decide
  have hdescent : baseEnd_6086709 < baseStart_6086709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086752 : List Nat := [2, 1, 1, 3, 2, 3, 2, 3, 1, 5]
def baseStart_6086752 : Nat := 118140960795 + 6086752 * 2 ^ 59
def prefixEnd_6086752 : Nat := 4983230072969 + 3 ^ 40 * 6086752 * 2
def baseEnd_6086752 : Nat := 1041809800238491596169181

theorem tailTrace_6086752 : CollatzResearch.WordTrace tailWord_6086752 prefixEnd_6086752 1041809800238491596169181 := by
  unfold tailWord_6086752
  simp only [CollatzResearch.WordTrace]
  refine ⟨111001041822372256662571255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148001389096496342216761673 111001041822372256662571255)
  ·
    refine ⟨166501562733558384993856883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111001041822372256662571255 166501562733558384993856883)
    ·
      refine ⟨249752344100337577490785325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166501562733558384993856883 249752344100337577490785325)
      ·
        refine ⟨93657129037626591559044497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249752344100337577490785325 93657129037626591559044497)
        ·
          refine ⟨70242846778219943669283373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93657129037626591559044497 70242846778219943669283373)
          ·
            refine ⟨26341067541832478875981265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70242846778219943669283373 26341067541832478875981265)
            ·
              refine ⟨19755800656374359156985949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26341067541832478875981265 19755800656374359156985949)
              ·
                refine ⟨7408425246140384683869731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19755800656374359156985949 7408425246140384683869731)
                ·
                  refine ⟨11112637869210577025804597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7408425246140384683869731 11112637869210577025804597)
                  ·
                    refine ⟨1041809800238491596169181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11112637869210577025804597 1041809800238491596169181)
                    ·
                      rfl

theorem cell23_6086752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 1, 5].length) (baseStart_6086752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086752 prefixEnd_6086752 := by exact prefixLift 6086752
  have htrace : WordTrace (prefixWord ++ tailWord_6086752) baseStart_6086752 baseEnd_6086752 := by
    simpa [prefixWord, tailWord_6086752, baseEnd_6086752] using wordTrace_append hprefix tailTrace_6086752
  have hstable : (prefixWord ++ tailWord_6086752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086752).length < 2 ^ (prefixWord ++ tailWord_6086752).sum := by decide
  have hdescent : baseEnd_6086752 < baseStart_6086752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086759 : List Nat := [1, 1, 5, 1, 1, 2, 3, 2, 2, 3, 2]
def baseStart_6086759 : Nat := 118140960795 + 6086759 * 2 ^ 59
def prefixEnd_6086759 : Nat := 4983230072969 + 3 ^ 40 * 6086759 * 2
def baseEnd_6086759 : Nat := 3125432995080056261120011

theorem tailTrace_6086759 : CollatzResearch.WordTrace tailWord_6086759 prefixEnd_6086759 3125432995080056261120011 := by
  unfold tailWord_6086759
  simp only [CollatzResearch.WordTrace]
  refine ⟨222002338955719153520647331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148001559303812769013764887 222002338955719153520647331)
  ·
    refine ⟨333003508433578730280970997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222002338955719153520647331 333003508433578730280970997)
    ·
      refine ⟨31219078915648005963841031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 333003508433578730280970997 31219078915648005963841031)
      ·
        refine ⟨46828618373472008945761547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31219078915648005963841031 46828618373472008945761547)
        ·
          refine ⟨70242927560208013418642321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46828618373472008945761547 70242927560208013418642321)
          ·
            refine ⟨52682195670156010063981741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70242927560208013418642321 52682195670156010063981741)
            ·
              refine ⟨19755823376308503773993153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52682195670156010063981741 19755823376308503773993153)
              ·
                refine ⟨14816867532231377830494865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19755823376308503773993153 14816867532231377830494865)
                ·
                  refine ⟨11112650649173533372871149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14816867532231377830494865 11112650649173533372871149)
                  ·
                    refine ⟨4167243993440075014826681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11112650649173533372871149 4167243993440075014826681)
                    ·
                      refine ⟨3125432995080056261120011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4167243993440075014826681 3125432995080056261120011)
                      ·
                        rfl

theorem cell23_6086759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_6086759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086759 prefixEnd_6086759 := by exact prefixLift 6086759
  have htrace : WordTrace (prefixWord ++ tailWord_6086759) baseStart_6086759 baseEnd_6086759 := by
    simpa [prefixWord, tailWord_6086759, baseEnd_6086759] using wordTrace_append hprefix tailTrace_6086759
  have hstable : (prefixWord ++ tailWord_6086759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086759).length < 2 ^ (prefixWord ++ tailWord_6086759).sum := by decide
  have hdescent : baseEnd_6086759 < baseStart_6086759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086789 : List Nat := [1, 3, 1, 1, 5, 1, 3, 2, 1, 1, 4]
def baseStart_6086789 : Nat := 118140960795 + 6086789 * 2 ^ 59
def prefixEnd_6086789 : Nat := 4983230072969 + 3 ^ 40 * 6086789 * 2
def baseEnd_6086789 : Nat := 3125448399499691143744873

theorem tailTrace_6086789 : CollatzResearch.WordTrace tailWord_6086789 prefixEnd_6086789 3125448399499691143744873 := by
  unfold tailWord_6086789
  simp only [CollatzResearch.WordTrace]
  refine ⟨222003433145610468644239421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148002288763740312429492947 222003433145610468644239421)
  ·
    refine ⟨83251287429603925741589783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222003433145610468644239421 83251287429603925741589783)
    ·
      refine ⟨124876931144405888612384675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83251287429603925741589783 124876931144405888612384675)
      ·
        refine ⟨187315396716608832918577013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124876931144405888612384675 187315396716608832918577013)
        ·
          refine ⟨17560818442182078086116595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 187315396716608832918577013 17560818442182078086116595)
          ·
            refine ⟨26341227663273117129174893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17560818442182078086116595 26341227663273117129174893)
            ·
              refine ⟨9877960373727418923440585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26341227663273117129174893 9877960373727418923440585)
              ·
                refine ⟨7408470280295564192580439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9877960373727418923440585 7408470280295564192580439)
                ·
                  refine ⟨11112705420443346288870659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7408470280295564192580439 11112705420443346288870659)
                  ·
                    refine ⟨16669058130665019433305989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11112705420443346288870659 16669058130665019433305989)
                    ·
                      refine ⟨3125448399499691143744873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16669058130665019433305989 3125448399499691143744873)
                      ·
                        rfl

theorem cell23_6086789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 1, 4].length) (baseStart_6086789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086789 prefixEnd_6086789 := by exact prefixLift 6086789
  have htrace : WordTrace (prefixWord ++ tailWord_6086789) baseStart_6086789 baseEnd_6086789 := by
    simpa [prefixWord, tailWord_6086789, baseEnd_6086789] using wordTrace_append hprefix tailTrace_6086789
  have hstable : (prefixWord ++ tailWord_6086789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086789).length < 2 ^ (prefixWord ++ tailWord_6086789).sum := by decide
  have hdescent : baseEnd_6086789 < baseStart_6086789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086829 : List Nat := [1, 5, 2, 1, 2, 3, 1, 8]
def baseStart_6086829 : Nat := 118140960795 + 6086829 * 2 ^ 59
def prefixEnd_6086829 : Nat := 4983230072969 + 3 ^ 40 * 6086829 * 2
def baseEnd_6086829 : Nat := 115758108841698925453507

theorem tailTrace_6086829 : CollatzResearch.WordTrace tailWord_6086829 prefixEnd_6086829 115758108841698925453507 := by
  unfold tailWord_6086829
  simp only [CollatzResearch.WordTrace]
  refine ⟨222004892065465555475695541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148003261376977036983797027 222004892065465555475695541)
  ·
    refine ⟨20812958631137395825846457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 222004892065465555475695541 20812958631137395825846457)
    ·
      refine ⟨15609718973353046869384843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20812958631137395825846457 15609718973353046869384843)
      ·
        refine ⟨23414578460029570304077265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15609718973353046869384843 23414578460029570304077265)
        ·
          refine ⟨17560933845022177728057949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23414578460029570304077265 17560933845022177728057949)
          ·
            refine ⟨6585350191883316648021731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17560933845022177728057949 6585350191883316648021731)
            ·
              refine ⟨9878025287824974972032597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6585350191883316648021731 9878025287824974972032597)
              ·
                refine ⟨115758108841698925453507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9878025287824974972032597 115758108841698925453507)
                ·
                  rfl

theorem cell23_6086829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 8].length) (baseStart_6086829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086829 prefixEnd_6086829 := by exact prefixLift 6086829
  have htrace : WordTrace (prefixWord ++ tailWord_6086829) baseStart_6086829 baseEnd_6086829 := by
    simpa [prefixWord, tailWord_6086829, baseEnd_6086829] using wordTrace_append hprefix tailTrace_6086829
  have hstable : (prefixWord ++ tailWord_6086829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086829).length < 2 ^ (prefixWord ++ tailWord_6086829).sum := by decide
  have hdescent : baseEnd_6086829 < baseStart_6086829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086832 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 1, 9, 2]
def baseStart_6086832 : Nat := 118140960795 + 6086832 * 2 ^ 59
def prefixEnd_6086832 : Nat := 4983230072969 + 3 ^ 40 * 6086832 * 2
def baseEnd_6086832 : Nat := 3125470479167834475507175

theorem tailTrace_6086832 : CollatzResearch.WordTrace tailWord_6086832 prefixEnd_6086832 3125470479167834475507175 := by
  unfold tailWord_6086832
  simp only [CollatzResearch.WordTrace]
  refine ⟨111002500742227343494027375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148003334322969791325369833 111002500742227343494027375)
  ·
    refine ⟨166503751113341015241041063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111002500742227343494027375 166503751113341015241041063)
    ·
      refine ⟨249755626670011522861561595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166503751113341015241041063 249755626670011522861561595)
      ·
        refine ⟨374633440005017284292342393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249755626670011522861561595 374633440005017284292342393)
        ·
          refine ⟨280975080003762963219256795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374633440005017284292342393 280975080003762963219256795)
          ·
            refine ⟨421462620005644444828885193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280975080003762963219256795 421462620005644444828885193)
            ·
              refine ⟨316096965004233333621663895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 421462620005644444828885193 316096965004233333621663895)
              ·
                refine ⟨474145447506350000432495843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 316096965004233333621663895 474145447506350000432495843)
                ·
                  refine ⟨711218171259525000648743765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 474145447506350000432495843 711218171259525000648743765)
                  ·
                    refine ⟨4167293972223779300676233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 711218171259525000648743765 4167293972223779300676233)
                    ·
                      refine ⟨3125470479167834475507175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4167293972223779300676233 3125470479167834475507175)
                      ·
                        rfl

theorem cell23_6086832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 1, 9, 2].length) (baseStart_6086832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086832 prefixEnd_6086832 := by exact prefixLift 6086832
  have htrace : WordTrace (prefixWord ++ tailWord_6086832) baseStart_6086832 baseEnd_6086832 := by
    simpa [prefixWord, tailWord_6086832, baseEnd_6086832] using wordTrace_append hprefix tailTrace_6086832
  have hstable : (prefixWord ++ tailWord_6086832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086832).length < 2 ^ (prefixWord ++ tailWord_6086832).sum := by decide
  have hdescent : baseEnd_6086832 < baseStart_6086832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086835 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 5]
def baseStart_6086835 : Nat := 118140960795 + 6086835 * 2 ^ 59
def prefixEnd_6086835 : Nat := 4983230072969 + 3 ^ 40 * 6086835 * 2
def baseEnd_6086835 : Nat := 3125472019609797963769661

theorem tailTrace_6086835 : CollatzResearch.WordTrace tailWord_6086835 prefixEnd_6086835 3125472019609797963769661 := by
  unfold tailWord_6086835
  simp only [CollatzResearch.WordTrace]
  refine ⟨222005110903443818500413959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148003407268962545666942639 222005110903443818500413959)
  ·
    refine ⟨333007666355165727750620939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222005110903443818500413959 333007666355165727750620939)
    ·
      refine ⟨499511499532748591625931409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333007666355165727750620939 499511499532748591625931409)
      ·
        refine ⟨374633624649561443719448557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 499511499532748591625931409 374633624649561443719448557)
        ·
          refine ⟨140487609243585541394793209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 374633624649561443719448557 140487609243585541394793209)
          ·
            refine ⟨105365706932689156046094907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140487609243585541394793209 105365706932689156046094907)
            ·
              refine ⟨158048560399033734069142361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105365706932689156046094907 158048560399033734069142361)
              ·
                refine ⟨118536420299275300551856771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158048560399033734069142361 118536420299275300551856771)
                ·
                  refine ⟨177804630448912950827785157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118536420299275300551856771 177804630448912950827785157)
                  ·
                    refine ⟨33338368209171178280209717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 177804630448912950827785157 33338368209171178280209717)
                    ·
                      refine ⟨3125472019609797963769661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33338368209171178280209717 3125472019609797963769661)
                      ·
                        rfl

theorem cell23_6086835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 4, 5].length) (baseStart_6086835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086835 prefixEnd_6086835 := by exact prefixLift 6086835
  have htrace : WordTrace (prefixWord ++ tailWord_6086835) baseStart_6086835 baseEnd_6086835 := by
    simpa [prefixWord, tailWord_6086835, baseEnd_6086835] using wordTrace_append hprefix tailTrace_6086835
  have hstable : (prefixWord ++ tailWord_6086835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086835).length < 2 ^ (prefixWord ++ tailWord_6086835).sum := by decide
  have hdescent : baseEnd_6086835 < baseStart_6086835 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086839 : List Nat := [1, 1, 3, 1, 4, 3, 2, 1, 1, 3, 3]
def baseStart_6086839 : Nat := 118140960795 + 6086839 * 2 ^ 59
def prefixEnd_6086839 : Nat := 4983230072969 + 3 ^ 40 * 6086839 * 2
def baseEnd_6086839 : Nat := 3125474073532415948119643

theorem tailTrace_6086839 : CollatzResearch.WordTrace tailWord_6086839 prefixEnd_6086839 3125474073532415948119643 := by
  unfold tailWord_6086839
  simp only [CollatzResearch.WordTrace]
  refine ⟨222005256795429327183559571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148003504530286218122373047 222005256795429327183559571)
  ·
    refine ⟨333007885193143990775339357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222005256795429327183559571 333007885193143990775339357)
    ·
      refine ⟨124877956947428996540752259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 333007885193143990775339357 124877956947428996540752259)
      ·
        refine ⟨187316935421143494811128389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124877956947428996540752259 187316935421143494811128389)
        ·
          refine ⟨35121925391464405277086573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 187316935421143494811128389 35121925391464405277086573)
          ·
            refine ⟨13170722021799151978907465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35121925391464405277086573 13170722021799151978907465)
            ·
              refine ⟨9878041516349363984180599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13170722021799151978907465 9878041516349363984180599)
              ·
                refine ⟨14817062274524045976270899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9878041516349363984180599 14817062274524045976270899)
                ·
                  refine ⟨22225593411786068964406349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14817062274524045976270899 22225593411786068964406349)
                  ·
                    refine ⟨8334597529419775861652381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22225593411786068964406349 8334597529419775861652381)
                    ·
                      refine ⟨3125474073532415948119643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8334597529419775861652381 3125474073532415948119643)
                      ·
                        rfl

theorem cell23_6086839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 3, 3].length) (baseStart_6086839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086839 prefixEnd_6086839 := by exact prefixLift 6086839
  have htrace : WordTrace (prefixWord ++ tailWord_6086839) baseStart_6086839 baseEnd_6086839 := by
    simpa [prefixWord, tailWord_6086839, baseEnd_6086839] using wordTrace_append hprefix tailTrace_6086839
  have hstable : (prefixWord ++ tailWord_6086839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086839).length < 2 ^ (prefixWord ++ tailWord_6086839).sum := by decide
  have hdescent : baseEnd_6086839 < baseStart_6086839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086860 : List Nat := [2, 2, 1, 6, 1, 2, 2, 1, 1, 2, 3]
def baseStart_6086860 : Nat := 118140960795 + 6086860 * 2 ^ 59
def prefixEnd_6086860 : Nat := 4983230072969 + 3 ^ 40 * 6086860 * 2
def baseEnd_6086860 : Nat := 3125484856626160365957047

theorem tailTrace_6086860 : CollatzResearch.WordTrace tailWord_6086860 prefixEnd_6086860 3125484856626160365957047 := by
  unfold tailWord_6086860
  simp only [CollatzResearch.WordTrace]
  refine ⟨111003011364176623885037017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148004015152235498513382689 111003011364176623885037017)
  ·
    refine ⟨83252258523132467913777763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111003011364176623885037017 83252258523132467913777763)
    ·
      refine ⟨124878387784698701870666645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83252258523132467913777763 124878387784698701870666645)
      ·
        refine ⟨5853674427407751650187499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 124878387784698701870666645 5853674427407751650187499)
        ·
          refine ⟨8780511641111627475281249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5853674427407751650187499 8780511641111627475281249)
          ·
            refine ⟨6585383730833720606460937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8780511641111627475281249 6585383730833720606460937)
            ·
              refine ⟨4939037798125290454845703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6585383730833720606460937 4939037798125290454845703)
              ·
                refine ⟨7408556697187935682268555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4939037798125290454845703 7408556697187935682268555)
                ·
                  refine ⟨11112835045781903523402833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7408556697187935682268555 11112835045781903523402833)
                  ·
                    refine ⟨8334626284336427642552125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11112835045781903523402833 8334626284336427642552125)
                    ·
                      refine ⟨3125484856626160365957047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8334626284336427642552125 3125484856626160365957047)
                      ·
                        rfl

theorem cell23_6086860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_6086860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086860 prefixEnd_6086860 := by exact prefixLift 6086860
  have htrace : WordTrace (prefixWord ++ tailWord_6086860) baseStart_6086860 baseEnd_6086860 := by
    simpa [prefixWord, tailWord_6086860, baseEnd_6086860] using wordTrace_append hprefix tailTrace_6086860
  have hstable : (prefixWord ++ tailWord_6086860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086860).length < 2 ^ (prefixWord ++ tailWord_6086860).sum := by decide
  have hdescent : baseEnd_6086860 < baseStart_6086860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086872 : List Nat := [2, 1, 2, 2, 4, 1, 1, 2, 2, 6]
def baseStart_6086872 : Nat := 118140960795 + 6086872 * 2 ^ 59
def prefixEnd_6086872 : Nat := 4983230072969 + 3 ^ 40 * 6086872 * 2
def baseEnd_6086872 : Nat := 1041830339464671439668997

theorem tailTrace_6086872 : CollatzResearch.WordTrace tailWord_6086872 prefixEnd_6086872 1041830339464671439668997 := by
  unfold tailWord_6086872
  simp only [CollatzResearch.WordTrace]
  refine ⟨111003230202154886909755435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148004306936206515879673913 111003230202154886909755435)
  ·
    refine ⟨166504845303232330364633153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111003230202154886909755435 166504845303232330364633153)
    ·
      refine ⟨124878633977424247773474865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166504845303232330364633153 124878633977424247773474865)
      ·
        refine ⟨93658975483068185830106149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124878633977424247773474865 93658975483068185830106149)
        ·
          refine ⟨17561057903075284843144903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93658975483068185830106149 17561057903075284843144903)
          ·
            refine ⟨26341586854612927264717355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17561057903075284843144903 26341586854612927264717355)
            ·
              refine ⟨39512380281919390897076033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26341586854612927264717355 39512380281919390897076033)
              ·
                refine ⟨29634285211439543172807025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39512380281919390897076033 29634285211439543172807025)
                ·
                  refine ⟨22225713908579657379605269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29634285211439543172807025 22225713908579657379605269)
                  ·
                    refine ⟨1041830339464671439668997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22225713908579657379605269 1041830339464671439668997)
                    ·
                      rfl

theorem cell23_6086872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 2, 6].length) (baseStart_6086872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086872 prefixEnd_6086872 := by exact prefixLift 6086872
  have htrace : WordTrace (prefixWord ++ tailWord_6086872) baseStart_6086872 baseEnd_6086872 := by
    simpa [prefixWord, tailWord_6086872, baseEnd_6086872] using wordTrace_append hprefix tailTrace_6086872
  have hstable : (prefixWord ++ tailWord_6086872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086872).length < 2 ^ (prefixWord ++ tailWord_6086872).sum := by decide
  have hdescent : baseEnd_6086872 < baseStart_6086872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086875 : List Nat := [1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 6]
def baseStart_6086875 : Nat := 118140960795 + 6086875 * 2 ^ 59
def prefixEnd_6086875 : Nat := 4983230072969 + 3 ^ 40 * 6086875 * 2
def baseEnd_6086875 : Nat := 3125492558835977807269477

theorem tailTrace_6086875 : CollatzResearch.WordTrace tailWord_6086875 prefixEnd_6086875 3125492558835977807269477 := by
  unfold tailWord_6086875
  simp only [CollatzResearch.WordTrace]
  refine ⟨222006569823298905331870079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148004379882199270221246719 222006569823298905331870079)
  ·
    refine ⟨333009854734948357997805119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222006569823298905331870079 333009854734948357997805119)
    ·
      refine ⟨499514782102422536996707679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333009854734948357997805119 499514782102422536996707679)
      ·
        refine ⟨749272173153633805495061519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 499514782102422536996707679 749272173153633805495061519)
        ·
          refine ⟨1123908259730450708242592279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 749272173153633805495061519 1123908259730450708242592279)
          ·
            refine ⟨1685862389595676062363888419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1123908259730450708242592279 1685862389595676062363888419)
            ·
              refine ⟨2528793584393514093545832629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1685862389595676062363888419 2528793584393514093545832629)
              ·
                refine ⟨237074398536891946269921809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2528793584393514093545832629 237074398536891946269921809)
                ·
                  refine ⟨177805798902668959702441357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 237074398536891946269921809 177805798902668959702441357)
                  ·
                    refine ⟨66677174588500859888415509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 177805798902668959702441357 66677174588500859888415509)
                    ·
                      refine ⟨3125492558835977807269477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66677174588500859888415509 3125492558835977807269477)
                      ·
                        rfl

theorem cell23_6086875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3, 6].length) (baseStart_6086875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086875 prefixEnd_6086875 := by exact prefixLift 6086875
  have htrace : WordTrace (prefixWord ++ tailWord_6086875) baseStart_6086875 baseEnd_6086875 := by
    simpa [prefixWord, tailWord_6086875, baseEnd_6086875] using wordTrace_append hprefix tailTrace_6086875
  have hstable : (prefixWord ++ tailWord_6086875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086875).length < 2 ^ (prefixWord ++ tailWord_6086875).sum := by decide
  have hdescent : baseEnd_6086875 < baseStart_6086875 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086892 : List Nat := [2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 4]
def baseStart_6086892 : Nat := 118140960795 + 6086892 * 2 ^ 59
def prefixEnd_6086892 : Nat := 4983230072969 + 3 ^ 40 * 6086892 * 2
def baseEnd_6086892 : Nat := 3125501288007104240756899

theorem tailTrace_6086892 : CollatzResearch.WordTrace tailWord_6086892 prefixEnd_6086892 3125501288007104240756899 := by
  unfold tailWord_6086892
  simp only [CollatzResearch.WordTrace]
  refine ⟨111003594932118658617619465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148004793242824878156825953 111003594932118658617619465)
  ·
    refine ⟨83252696199088993963214599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111003594932118658617619465 83252696199088993963214599)
    ·
      refine ⟨124879044298633490944821899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83252696199088993963214599 124879044298633490944821899)
      ·
        refine ⟨187318566447950236417232849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124879044298633490944821899 187318566447950236417232849)
        ·
          refine ⟨140488924835962677312924637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187318566447950236417232849 140488924835962677312924637)
          ·
            refine ⟨52683346813486003992346739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140488924835962677312924637 52683346813486003992346739)
            ·
              refine ⟨79025020220229005988520109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52683346813486003992346739 79025020220229005988520109)
              ·
                refine ⟨29634382582585877245695041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79025020220229005988520109 29634382582585877245695041)
                ·
                  refine ⟨22225786936939407934271281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29634382582585877245695041 22225786936939407934271281)
                  ·
                    refine ⟨16669340202704555950703461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22225786936939407934271281 16669340202704555950703461)
                    ·
                      refine ⟨3125501288007104240756899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16669340202704555950703461 3125501288007104240756899)
                      ·
                        rfl

theorem cell23_6086892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 4].length) (baseStart_6086892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086892 prefixEnd_6086892 := by exact prefixLift 6086892
  have htrace : WordTrace (prefixWord ++ tailWord_6086892) baseStart_6086892 baseEnd_6086892 := by
    simpa [prefixWord, tailWord_6086892, baseEnd_6086892] using wordTrace_append hprefix tailTrace_6086892
  have hstable : (prefixWord ++ tailWord_6086892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086892).length < 2 ^ (prefixWord ++ tailWord_6086892).sum := by decide
  have hdescent : baseEnd_6086892 < baseStart_6086892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086896 : List Nat := [2, 1, 1, 1, 3, 1, 1, 7, 2, 2, 2]
def baseStart_6086896 : Nat := 118140960795 + 6086896 * 2 ^ 59
def prefixEnd_6086896 : Nat := 4983230072969 + 3 ^ 40 * 6086896 * 2
def baseEnd_6086896 : Nat := 3125503341929722225106881

theorem tailTrace_6086896 : CollatzResearch.WordTrace tailWord_6086896 prefixEnd_6086896 3125503341929722225106881 := by
  unfold tailWord_6086896
  simp only [CollatzResearch.WordTrace]
  refine ⟨111003667878111412959192271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148004890504148550612256361 111003667878111412959192271)
  ·
    refine ⟨166505501817167119438788407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111003667878111412959192271 166505501817167119438788407)
    ·
      refine ⟨249758252725750679158182611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166505501817167119438788407 249758252725750679158182611)
      ·
        refine ⟨374637379088626018737273917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249758252725750679158182611 374637379088626018737273917)
        ·
          refine ⟨140489017158234757026477719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 374637379088626018737273917 140489017158234757026477719)
          ·
            refine ⟨210733525737352135539716579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140489017158234757026477719 210733525737352135539716579)
            ·
              refine ⟨316100288606028203309574869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210733525737352135539716579 316100288606028203309574869)
              ·
                refine ⟨7408600514203786015068161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 316100288606028203309574869 7408600514203786015068161)
                ·
                  refine ⟨5556450385652839511301121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7408600514203786015068161 5556450385652839511301121)
                  ·
                    refine ⟨4167337789239629633475841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5556450385652839511301121 4167337789239629633475841)
                    ·
                      refine ⟨3125503341929722225106881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4167337789239629633475841 3125503341929722225106881)
                      ·
                        rfl

theorem cell23_6086896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 7, 2, 2, 2].length) (baseStart_6086896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086896 prefixEnd_6086896 := by exact prefixLift 6086896
  have htrace : WordTrace (prefixWord ++ tailWord_6086896) baseStart_6086896 baseEnd_6086896 := by
    simpa [prefixWord, tailWord_6086896, baseEnd_6086896] using wordTrace_append hprefix tailTrace_6086896
  have hstable : (prefixWord ++ tailWord_6086896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086896).length < 2 ^ (prefixWord ++ tailWord_6086896).sum := by decide
  have hdescent : baseEnd_6086896 < baseStart_6086896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086912 : List Nat := [2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 3]
def baseStart_6086912 : Nat := 118140960795 + 6086912 * 2 ^ 59
def prefixEnd_6086912 : Nat := 4983230072969 + 3 ^ 40 * 6086912 * 2
def baseEnd_6086912 : Nat := 3125511557620194162506807

theorem tailTrace_6086912 : CollatzResearch.WordTrace tailWord_6086912 prefixEnd_6086912 3125511557620194162506807 := by
  unfold tailWord_6086912
  simp only [CollatzResearch.WordTrace]
  refine ⟨111003959662082430325483495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148005279549443240433977993 111003959662082430325483495)
  ·
    refine ⟨166505939493123645488225243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111003959662082430325483495 166505939493123645488225243)
    ·
      refine ⟨249758909239685468232337865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166505939493123645488225243 249758909239685468232337865)
      ·
        refine ⟨187319181929764101174253399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249758909239685468232337865 187319181929764101174253399)
        ·
          refine ⟨280978772894646151761380099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187319181929764101174253399 280978772894646151761380099)
          ·
            refine ⟨421468159341969227642070149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280978772894646151761380099 421468159341969227642070149)
            ·
              refine ⟨79025279876619230182888153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 421468159341969227642070149 79025279876619230182888153)
              ·
                refine ⟨59268959907464422637166115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79025279876619230182888153 59268959907464422637166115)
                ·
                  refine ⟨88903439861196633955749173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59268959907464422637166115 88903439861196633955749173)
                  ·
                    refine ⟨8334697486987184433351485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88903439861196633955749173 8334697486987184433351485)
                    ·
                      refine ⟨3125511557620194162506807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8334697486987184433351485 3125511557620194162506807)
                      ·
                        rfl

theorem cell23_6086912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 1, 5, 3].length) (baseStart_6086912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086912 prefixEnd_6086912 := by exact prefixLift 6086912
  have htrace : WordTrace (prefixWord ++ tailWord_6086912) baseStart_6086912 baseEnd_6086912 := by
    simpa [prefixWord, tailWord_6086912, baseEnd_6086912] using wordTrace_append hprefix tailTrace_6086912
  have hstable : (prefixWord ++ tailWord_6086912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086912).length < 2 ^ (prefixWord ++ tailWord_6086912).sum := by decide
  have hdescent : baseEnd_6086912 < baseStart_6086912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6086936 : List Nat := [2, 1, 2, 3, 1, 2, 5, 2, 5]
def baseStart_6086936 : Nat := 118140960795 + 6086936 * 2 ^ 59
def prefixEnd_6086936 : Nat := 4983230072969 + 3 ^ 40 * 6086936 * 2
def baseEnd_6086936 : Nat := 347280431239544674289633

theorem tailTrace_6086936 : CollatzResearch.WordTrace tailWord_6086936 prefixEnd_6086936 347280431239544674289633 := by
  unfold tailWord_6086936
  simp only [CollatzResearch.WordTrace]
  refine ⟨111004397338038956374920331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148005863117385275166560441 111004397338038956374920331)
  ·
    refine ⟨166506596007058434562380497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111004397338038956374920331 166506596007058434562380497)
    ·
      refine ⟨124879947005293825921785373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166506596007058434562380497 124879947005293825921785373)
      ·
        refine ⟨46829980126985184720669515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124879947005293825921785373 46829980126985184720669515)
        ·
          refine ⟨70244970190477777081004273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46829980126985184720669515 70244970190477777081004273)
          ·
            refine ⟨52683727642858332810753205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70244970190477777081004273 52683727642858332810753205)
            ·
              refine ⟨4939099466517968701008113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52683727642858332810753205 4939099466517968701008113)
              ·
                refine ⟨3704324599888476525756085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4939099466517968701008113 3704324599888476525756085)
                ·
                  refine ⟨347280431239544674289633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3704324599888476525756085 347280431239544674289633)
                  ·
                    rfl

theorem cell23_6086936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 2, 5].length) (baseStart_6086936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6086936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6086936 prefixEnd_6086936 := by exact prefixLift 6086936
  have htrace : WordTrace (prefixWord ++ tailWord_6086936) baseStart_6086936 baseEnd_6086936 := by
    simpa [prefixWord, tailWord_6086936, baseEnd_6086936] using wordTrace_append hprefix tailTrace_6086936
  have hstable : (prefixWord ++ tailWord_6086936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6086936).length < 2 ^ (prefixWord ++ tailWord_6086936).sum := by decide
  have hdescent : baseEnd_6086936 < baseStart_6086936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6086936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087039 : List Nat := [1, 1, 2, 2, 1, 1, 2, 7, 1, 5]
def baseStart_6087039 : Nat := 118140960795 + 6087039 * 2 ^ 59
def prefixEnd_6087039 : Nat := 4983230072969 + 3 ^ 40 * 6087039 * 2
def baseEnd_6087039 : Nat := 1041858923221105055206241

theorem tailTrace_6087039 : CollatzResearch.WordTrace tailWord_6087039 prefixEnd_6087039 1041858923221105055206241 := by
  unfold tailWord_6087039
  simp only [CollatzResearch.WordTrace]
  refine ⟨222012551394704761340840171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148008367596469840893893447 222012551394704761340840171)
  ·
    refine ⟨333018827092057142011260257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222012551394704761340840171 333018827092057142011260257)
    ·
      refine ⟨249764120319042856508445193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333018827092057142011260257 249764120319042856508445193)
      ·
        refine ⟨187323090239282142381333895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249764120319042856508445193 187323090239282142381333895)
        ·
          refine ⟨280984635358923213572000843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187323090239282142381333895 280984635358923213572000843)
          ·
            refine ⟨421476953038384820358001265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280984635358923213572000843 421476953038384820358001265)
            ·
              refine ⟨316107714778788615268500949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 421476953038384820358001265 316107714778788615268500949)
              ·
                refine ⟨7408774565127858170355491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 316107714778788615268500949 7408774565127858170355491)
                ·
                  refine ⟨11113161847691787255533237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7408774565127858170355491 11113161847691787255533237)
                  ·
                    refine ⟨1041858923221105055206241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11113161847691787255533237 1041858923221105055206241)
                    ·
                      rfl

theorem cell23_6087039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 5].length) (baseStart_6087039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087039 prefixEnd_6087039 := by exact prefixLift 6087039
  have htrace : WordTrace (prefixWord ++ tailWord_6087039) baseStart_6087039 baseEnd_6087039 := by
    simpa [prefixWord, tailWord_6087039, baseEnd_6087039] using wordTrace_append hprefix tailTrace_6087039
  have hstable : (prefixWord ++ tailWord_6087039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087039).length < 2 ^ (prefixWord ++ tailWord_6087039).sum := by decide
  have hdescent : baseEnd_6087039 < baseStart_6087039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087043 : List Nat := [1, 1, 1, 3, 7, 1, 1, 2, 6]
def baseStart_6087043 : Nat := 118140960795 + 6087043 * 2 ^ 59
def prefixEnd_6087043 : Nat := 4983230072969 + 3 ^ 40 * 6087043 * 2
def baseEnd_6087043 : Nat := 347286535953992572218745

theorem tailTrace_6087043 : CollatzResearch.WordTrace tailWord_6087043 prefixEnd_6087043 347286535953992572218745 := by
  unfold tailWord_6087043
  simp only [CollatzResearch.WordTrace]
  refine ⟨222012697286690270023985783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148008464857793513349323855 222012697286690270023985783)
  ·
    refine ⟨333019045930035405035978675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222012697286690270023985783 333019045930035405035978675)
    ·
      refine ⟨499528568895053107553968013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333019045930035405035978675 499528568895053107553968013)
      ·
        refine ⟨187323213335644915332738005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 499528568895053107553968013 187323213335644915332738005)
        ·
          refine ⟨4390387812554177703111047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 187323213335644915332738005 4390387812554177703111047)
          ·
            refine ⟨6585581718831266554666571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4390387812554177703111047 6585581718831266554666571)
            ·
              refine ⟨9878372578246899831999857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6585581718831266554666571 9878372578246899831999857)
              ·
                refine ⟨7408779433685174873999893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9878372578246899831999857 7408779433685174873999893)
                ·
                  refine ⟨347286535953992572218745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7408779433685174873999893 347286535953992572218745)
                  ·
                    rfl

theorem cell23_6087043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 6].length) (baseStart_6087043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087043 prefixEnd_6087043 := by exact prefixLift 6087043
  have htrace : WordTrace (prefixWord ++ tailWord_6087043) baseStart_6087043 baseEnd_6087043 := by
    simpa [prefixWord, tailWord_6087043, baseEnd_6087043] using wordTrace_append hprefix tailTrace_6087043
  have hstable : (prefixWord ++ tailWord_6087043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087043).length < 2 ^ (prefixWord ++ tailWord_6087043).sum := by decide
  have hdescent : baseEnd_6087043 < baseStart_6087043 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087070 : List Nat := [4, 3, 1, 2, 1, 1, 2, 2, 3, 1, 3]
def baseStart_6087070 : Nat := 118140960795 + 6087070 * 2 ^ 59
def prefixEnd_6087070 : Nat := 4983230072969 + 3 ^ 40 * 6087070 * 2
def baseEnd_6087070 : Nat := 3125592687563604544331081

theorem tailTrace_6087070 : CollatzResearch.WordTrace tailWord_6087070 prefixEnd_6087070 3125592687563604544331081 := by
  unfold tailWord_6087070
  simp only [CollatzResearch.WordTrace]
  refine ⟨27751710257199056704402333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148009121371728302423479109 27751710257199056704402333)
  ·
    refine ⟨10406891346449646264150875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27751710257199056704402333 10406891346449646264150875)
    ·
      refine ⟨15610337019674469396226313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10406891346449646264150875 15610337019674469396226313)
      ·
        refine ⟨11707752764755852047169735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15610337019674469396226313 11707752764755852047169735)
        ·
          refine ⟨17561629147133778070754603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11707752764755852047169735 17561629147133778070754603)
          ·
            refine ⟨26342443720700667106131905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17561629147133778070754603 26342443720700667106131905)
            ·
              refine ⟨19756832790525500329598929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26342443720700667106131905 19756832790525500329598929)
              ·
                refine ⟨14817624592894125247199197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19756832790525500329598929 14817624592894125247199197)
                ·
                  refine ⟨5556609222335296967699699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14817624592894125247199197 5556609222335296967699699)
                  ·
                    refine ⟨8334913833502945451549549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5556609222335296967699699 8334913833502945451549549)
                    ·
                      refine ⟨3125592687563604544331081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8334913833502945451549549 3125592687563604544331081)
                      ·
                        rfl

theorem cell23_6087070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_6087070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087070 prefixEnd_6087070 := by exact prefixLift 6087070
  have htrace : WordTrace (prefixWord ++ tailWord_6087070) baseStart_6087070 baseEnd_6087070 := by
    simpa [prefixWord, tailWord_6087070, baseEnd_6087070] using wordTrace_append hprefix tailTrace_6087070
  have hstable : (prefixWord ++ tailWord_6087070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087070).length < 2 ^ (prefixWord ++ tailWord_6087070).sum := by decide
  have hdescent : baseEnd_6087070 < baseStart_6087070 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087076 : List Nat := [2, 3, 1, 2, 1, 1, 3, 4, 1, 1, 4]
def baseStart_6087076 : Nat := 118140960795 + 6087076 * 2 ^ 59
def prefixEnd_6087076 : Nat := 4983230072969 + 3 ^ 40 * 6087076 * 2
def baseEnd_6087076 : Nat := 3125595768447531520856053

theorem tailTrace_6087076 : CollatzResearch.WordTrace tailWord_6087076 prefixEnd_6087076 3125595768447531520856053 := by
  unfold tailWord_6087076
  simp only [CollatzResearch.WordTrace]
  refine ⟨111006950447785358329968541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148009267263713811106624721 111006950447785358329968541)
  ·
    refine ⟨41627606417919509373738203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111006950447785358329968541 41627606417919509373738203)
    ·
      refine ⟨62441409626879264060607305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41627606417919509373738203 62441409626879264060607305)
      ·
        refine ⟨46831057220159448045455479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62441409626879264060607305 46831057220159448045455479)
        ·
          refine ⟨70246585830239172068183219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46831057220159448045455479 70246585830239172068183219)
          ·
            refine ⟨105369878745358758102274829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70246585830239172068183219 105369878745358758102274829)
            ·
              refine ⟨39513704529509534288353061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105369878745358758102274829 39513704529509534288353061)
              ·
                refine ⟨7408819599283037679066199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39513704529509534288353061 7408819599283037679066199)
                ·
                  refine ⟨11113229398924556518599299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7408819599283037679066199 11113229398924556518599299)
                  ·
                    refine ⟨16669844098386834777898949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11113229398924556518599299 16669844098386834777898949)
                    ·
                      refine ⟨3125595768447531520856053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16669844098386834777898949 3125595768447531520856053)
                      ·
                        rfl

theorem cell23_6087076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_6087076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087076 prefixEnd_6087076 := by exact prefixLift 6087076
  have htrace : WordTrace (prefixWord ++ tailWord_6087076) baseStart_6087076 baseEnd_6087076 := by
    simpa [prefixWord, tailWord_6087076, baseEnd_6087076] using wordTrace_append hprefix tailTrace_6087076
  have hstable : (prefixWord ++ tailWord_6087076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087076).length < 2 ^ (prefixWord ++ tailWord_6087076).sum := by decide
  have hdescent : baseEnd_6087076 < baseStart_6087076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087116 : List Nat := [2, 2, 1, 4, 3, 1, 2, 8]
def baseStart_6087116 : Nat := 118140960795 + 6087116 * 2 ^ 59
def prefixEnd_6087116 : Nat := 4983230072969 + 3 ^ 40 * 6087116 * 2
def baseEnd_6087116 : Nat := 115763566950878198679847

theorem tailTrace_6087116 : CollatzResearch.WordTrace tailWord_6087116 prefixEnd_6087116 115763566950878198679847 := by
  unfold tailWord_6087116
  simp only [CollatzResearch.WordTrace]
  refine ⟨111007679907712901745696601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148010239876950535660928801 111007679907712901745696601)
  ·
    refine ⟨83255759930784676309272451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111007679907712901745696601 83255759930784676309272451)
    ·
      refine ⟨124883639896177014463908677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83255759930784676309272451 124883639896177014463908677)
      ·
        refine ⟨23415682480533190211982877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124883639896177014463908677 23415682480533190211982877)
        ·
          refine ⟨8780880930199946329493579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23415682480533190211982877 8780880930199946329493579)
          ·
            refine ⟨13171321395299919494240369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8780880930199946329493579 13171321395299919494240369)
            ·
              refine ⟨9878491046474939620680277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13171321395299919494240369 9878491046474939620680277)
              ·
                refine ⟨115763566950878198679847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9878491046474939620680277 115763566950878198679847)
                ·
                  rfl

theorem cell23_6087116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 8].length) (baseStart_6087116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087116 prefixEnd_6087116 := by exact prefixLift 6087116
  have htrace : WordTrace (prefixWord ++ tailWord_6087116) baseStart_6087116 baseEnd_6087116 := by
    simpa [prefixWord, tailWord_6087116, baseEnd_6087116] using wordTrace_append hprefix tailTrace_6087116
  have hstable : (prefixWord ++ tailWord_6087116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087116).length < 2 ^ (prefixWord ++ tailWord_6087116).sum := by decide
  have hdescent : baseEnd_6087116 < baseStart_6087116 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087199 : List Nat := [1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 7]
def baseStart_6087199 : Nat := 118140960795 + 6087199 * 2 ^ 59
def prefixEnd_6087199 : Nat := 4983230072969 + 3 ^ 40 * 6087199 * 2
def baseEnd_6087199 : Nat := 3125658926568034539617987

theorem tailTrace_6087199 : CollatzResearch.WordTrace tailWord_6087199 prefixEnd_6087199 3125658926568034539617987 := by
  unfold tailWord_6087199
  simp only [CollatzResearch.WordTrace]
  refine ⟨222018387074125108666664651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148012258049416739111109767 222018387074125108666664651)
  ·
    refine ⟨333027580611187662999996977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222018387074125108666664651 333027580611187662999996977)
    ·
      refine ⟨249770685458390747249997733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333027580611187662999996977 249770685458390747249997733)
      ·
        refine ⟨46832003523448265109374575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 249770685458390747249997733 46832003523448265109374575)
        ·
          refine ⟨70248005285172397664061863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46832003523448265109374575 70248005285172397664061863)
          ·
            refine ⟨105372007927758596496092795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70248005285172397664061863 105372007927758596496092795)
            ·
              refine ⟨158058011891637894744139193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105372007927758596496092795 158058011891637894744139193)
              ·
                refine ⟨118543508918728421058104395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158058011891637894744139193 118543508918728421058104395)
                ·
                  refine ⟨177815263378092631587156593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118543508918728421058104395 177815263378092631587156593)
                  ·
                    refine ⟨133361447533569473690367445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 177815263378092631587156593 133361447533569473690367445)
                    ·
                      refine ⟨3125658926568034539617987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 133361447533569473690367445 3125658926568034539617987)
                      ·
                        rfl

theorem cell23_6087199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_6087199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087199 prefixEnd_6087199 := by exact prefixLift 6087199
  have htrace : WordTrace (prefixWord ++ tailWord_6087199) baseStart_6087199 baseEnd_6087199 := by
    simpa [prefixWord, tailWord_6087199, baseEnd_6087199] using wordTrace_append hprefix tailTrace_6087199
  have hstable : (prefixWord ++ tailWord_6087199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087199).length < 2 ^ (prefixWord ++ tailWord_6087199).sum := by decide
  have hdescent : baseEnd_6087199 < baseStart_6087199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087216 : List Nat := [2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 3]
def baseStart_6087216 : Nat := 118140960795 + 6087216 * 2 ^ 59
def prefixEnd_6087216 : Nat := 4983230072969 + 3 ^ 40 * 6087216 * 2
def baseEnd_6087216 : Nat := 3125667655739160973105409

theorem tailTrace_6087216 : CollatzResearch.WordTrace tailWord_6087216 prefixEnd_6087216 3125667655739160973105409 := by
  unfold tailWord_6087216
  simp only [CollatzResearch.WordTrace]
  refine ⟨111009503557531760285016751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148012671410042347046689001 111009503557531760285016751)
  ·
    refine ⟨166514255336297640427525127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111009503557531760285016751 166514255336297640427525127)
    ·
      refine ⟨249771383004446460641287691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166514255336297640427525127 249771383004446460641287691)
      ·
        refine ⟨374657074506669690961931537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249771383004446460641287691 374657074506669690961931537)
        ·
          refine ⟨280992805880002268221448653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374657074506669690961931537 280992805880002268221448653)
          ·
            refine ⟨105372302205000850583043245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 280992805880002268221448653 105372302205000850583043245)
            ·
              refine ⟨39514613326875318968641217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105372302205000850583043245 39514613326875318968641217)
              ·
                refine ⟨29635959995156489226480913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39514613326875318968641217 29635959995156489226480913)
                ·
                  refine ⟨22226969996367366919860685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29635959995156489226480913 22226969996367366919860685)
                  ·
                    refine ⟨8335113748637762594947757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22226969996367366919860685 8335113748637762594947757)
                    ·
                      refine ⟨3125667655739160973105409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8335113748637762594947757 3125667655739160973105409)
                      ·
                        rfl

theorem cell23_6087216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 3].length) (baseStart_6087216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087216 prefixEnd_6087216 := by exact prefixLift 6087216
  have htrace : WordTrace (prefixWord ++ tailWord_6087216) baseStart_6087216 baseEnd_6087216 := by
    simpa [prefixWord, tailWord_6087216, baseEnd_6087216] using wordTrace_append hprefix tailTrace_6087216
  have hstable : (prefixWord ++ tailWord_6087216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087216).length < 2 ^ (prefixWord ++ tailWord_6087216).sum := by decide
  have hdescent : baseEnd_6087216 < baseStart_6087216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087233 : List Nat := [1, 2, 5, 1, 1, 2, 2, 1, 2, 3, 3]
def baseStart_6087233 : Nat := 118140960795 + 6087233 * 2 ^ 59
def prefixEnd_6087233 : Nat := 4983230072969 + 3 ^ 40 * 6087233 * 2
def baseEnd_6087233 : Nat := 3125676384910287406592831

theorem tailTrace_6087233 : CollatzResearch.WordTrace tailWord_6087233 prefixEnd_6087233 3125676384910287406592831 := by
  unfold tailWord_6087233
  simp only [CollatzResearch.WordTrace]
  refine ⟨222019627156001932473402353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148013084770667954982268235 222019627156001932473402353)
  ·
    refine ⟨166514720367001449355051765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222019627156001932473402353 166514720367001449355051765)
    ·
      refine ⟨15610755034406385877036103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 166514720367001449355051765 15610755034406385877036103)
      ·
        refine ⟨23416132551609578815554155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15610755034406385877036103 23416132551609578815554155)
        ·
          refine ⟨35124198827414368223331233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23416132551609578815554155 35124198827414368223331233)
          ·
            refine ⟨26343149120560776167498425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35124198827414368223331233 26343149120560776167498425)
            ·
              refine ⟨19757361840420582125623819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26343149120560776167498425 19757361840420582125623819)
              ·
                refine ⟨29636042760630873188435729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19757361840420582125623819 29636042760630873188435729)
                ·
                  refine ⟨22227032070473154891326797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29636042760630873188435729 22227032070473154891326797)
                  ·
                    refine ⟨8335137026427433084247549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22227032070473154891326797 8335137026427433084247549)
                    ·
                      refine ⟨3125676384910287406592831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8335137026427433084247549 3125676384910287406592831)
                      ·
                        rfl

theorem cell23_6087233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_6087233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087233 prefixEnd_6087233 := by exact prefixLift 6087233
  have htrace : WordTrace (prefixWord ++ tailWord_6087233) baseStart_6087233 baseEnd_6087233 := by
    simpa [prefixWord, tailWord_6087233, baseEnd_6087233] using wordTrace_append hprefix tailTrace_6087233
  have hstable : (prefixWord ++ tailWord_6087233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087233).length < 2 ^ (prefixWord ++ tailWord_6087233).sum := by decide
  have hdescent : baseEnd_6087233 < baseStart_6087233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087256 : List Nat := [2, 1, 2, 2, 1, 2, 4, 1, 1, 3, 4]
def baseStart_6087256 : Nat := 118140960795 + 6087256 * 2 ^ 59
def prefixEnd_6087256 : Nat := 4983230072969 + 3 ^ 40 * 6087256 * 2
def baseEnd_6087256 : Nat := 3125688194965340816605225

theorem tailTrace_6087256 : CollatzResearch.WordTrace tailWord_6087256 prefixEnd_6087256 3125688194965340816605225 := by
  unfold tailWord_6087256
  simp only [CollatzResearch.WordTrace]
  refine ⟨111010233017459303700744811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148013644023279071600993081 111010233017459303700744811)
  ·
    refine ⟨166515349526188955551117217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111010233017459303700744811 166515349526188955551117217)
    ·
      refine ⟨124886512144641716663337913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166515349526188955551117217 124886512144641716663337913)
      ·
        refine ⟨93664884108481287497503435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124886512144641716663337913 93664884108481287497503435)
        ·
          refine ⟨140497326162721931246255153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93664884108481287497503435 140497326162721931246255153)
          ·
            refine ⟨105372994622041448434691365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140497326162721931246255153 105372994622041448434691365)
            ·
              refine ⟨19757436491632771581504631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105372994622041448434691365 19757436491632771581504631)
              ·
                refine ⟨29636154737449157372256947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19757436491632771581504631 29636154737449157372256947)
                ·
                  refine ⟨44454232106173736058385421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29636154737449157372256947 44454232106173736058385421)
                  ·
                    refine ⟨16670337039815151021894533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44454232106173736058385421 16670337039815151021894533)
                    ·
                      refine ⟨3125688194965340816605225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16670337039815151021894533 3125688194965340816605225)
                      ·
                        rfl

theorem cell23_6087256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_6087256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087256 prefixEnd_6087256 := by exact prefixLift 6087256
  have htrace : WordTrace (prefixWord ++ tailWord_6087256) baseStart_6087256 baseEnd_6087256 := by
    simpa [prefixWord, tailWord_6087256, baseEnd_6087256] using wordTrace_append hprefix tailTrace_6087256
  have hstable : (prefixWord ++ tailWord_6087256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087256).length < 2 ^ (prefixWord ++ tailWord_6087256).sum := by decide
  have hdescent : baseEnd_6087256 < baseStart_6087256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087310 : List Nat := [4, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3]
def baseStart_6087310 : Nat := 118140960795 + 6087310 * 2 ^ 59
def prefixEnd_6087310 : Nat := 4983230072969 + 3 ^ 40 * 6087310 * 2
def baseEnd_6087310 : Nat := 3125715922920683605329977

theorem tailTrace_6087310 : CollatzResearch.WordTrace tailWord_6087310 prefixEnd_6087310 3125715922920683605329977 := by
  unfold tailWord_6087310
  simp only [CollatzResearch.WordTrace]
  refine ⟨27752804447090371827994423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148014957051148649749303589 27752804447090371827994423)
  ·
    refine ⟨41629206670635557741991635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27752804447090371827994423 41629206670635557741991635)
    ·
      refine ⟨62443810005953336612987453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41629206670635557741991635 62443810005953336612987453)
      ·
        refine ⟨23416428752232501229870295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62443810005953336612987453 23416428752232501229870295)
        ·
          refine ⟨35124643128348751844805443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23416428752232501229870295 35124643128348751844805443)
          ·
            refine ⟨52686964692523127767208165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35124643128348751844805443 52686964692523127767208165)
            ·
              refine ⟨9878805879848086456351531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52686964692523127767208165 9878805879848086456351531)
              ·
                refine ⟨14818208819772129684527297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9878805879848086456351531 14818208819772129684527297)
                ·
                  refine ⟨11113656614829097263395473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14818208819772129684527297 11113656614829097263395473)
                  ·
                    refine ⟨8335242461121822947546605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11113656614829097263395473 8335242461121822947546605)
                    ·
                      refine ⟨3125715922920683605329977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8335242461121822947546605 3125715922920683605329977)
                      ·
                        rfl

theorem cell23_6087310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_6087310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087310 prefixEnd_6087310 := by exact prefixLift 6087310
  have htrace : WordTrace (prefixWord ++ tailWord_6087310) baseStart_6087310 baseEnd_6087310 := by
    simpa [prefixWord, tailWord_6087310, baseEnd_6087310] using wordTrace_append hprefix tailTrace_6087310
  have hstable : (prefixWord ++ tailWord_6087310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087310).length < 2 ^ (prefixWord ++ tailWord_6087310).sum := by decide
  have hdescent : baseEnd_6087310 < baseStart_6087310 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087333 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 3, 5, 2]
def baseStart_6087333 : Nat := 118140960795 + 6087333 * 2 ^ 59
def prefixEnd_6087333 : Nat := 4983230072969 + 3 ^ 40 * 6087333 * 2
def baseEnd_6087333 : Nat := 3125727732975737015342371

theorem tailTrace_6087333 : CollatzResearch.WordTrace tailWord_6087333 prefixEnd_6087333 3125727732975737015342371 := by
  unfold tailWord_6087333
  simp only [CollatzResearch.WordTrace]
  refine ⟨222023274455639649552042653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148015516303759766368028435 222023274455639649552042653)
  ·
    refine ⟨83258727920864868582015995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222023274455639649552042653 83258727920864868582015995)
    ·
      refine ⟨124888091881297302873023993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83258727920864868582015995 124888091881297302873023993)
      ·
        refine ⟨93666068910972977154767995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124888091881297302873023993 93666068910972977154767995)
        ·
          refine ⟨140499103366459465732151993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93666068910972977154767995 140499103366459465732151993)
          ·
            refine ⟨105374327524844599299113995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140499103366459465732151993 105374327524844599299113995)
            ·
              refine ⟨158061491287266898948670993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105374327524844599299113995 158061491287266898948670993)
              ·
                refine ⟨118546118465450174211503245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158061491287266898948670993 118546118465450174211503245)
                ·
                  refine ⟨44454794424543815329313717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118546118465450174211503245 44454794424543815329313717)
                  ·
                    refine ⟨4167636977300982687123161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44454794424543815329313717 4167636977300982687123161)
                    ·
                      refine ⟨3125727732975737015342371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4167636977300982687123161 3125727732975737015342371)
                      ·
                        rfl

theorem cell23_6087333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 5, 2].length) (baseStart_6087333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087333 prefixEnd_6087333 := by exact prefixLift 6087333
  have htrace : WordTrace (prefixWord ++ tailWord_6087333) baseStart_6087333 baseEnd_6087333 := by
    simpa [prefixWord, tailWord_6087333, baseEnd_6087333] using wordTrace_append hprefix tailTrace_6087333
  have hstable : (prefixWord ++ tailWord_6087333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087333).length < 2 ^ (prefixWord ++ tailWord_6087333).sum := by decide
  have hdescent : baseEnd_6087333 < baseStart_6087333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087361 : List Nat := [1, 2, 6, 2, 2, 1, 1, 1, 2, 2, 3]
def baseStart_6087361 : Nat := 118140960795 + 6087361 * 2 ^ 59
def prefixEnd_6087361 : Nat := 4983230072969 + 3 ^ 40 * 6087361 * 2
def baseEnd_6087361 : Nat := 3125742110434062905792243

theorem tailTrace_6087361 : CollatzResearch.WordTrace tailWord_6087361 prefixEnd_6087361 3125742110434062905792243 := by
  unfold tailWord_6087361
  simp only [CollatzResearch.WordTrace]
  refine ⟨222024295699538210334061937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148016197133025473556041291 222024295699538210334061937)
  ·
    refine ⟨166518221774653657750546453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222024295699538210334061937 166518221774653657750546453)
    ·
      refine ⟨7805541645686890207056865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 166518221774653657750546453 7805541645686890207056865)
      ·
        refine ⟨5854156234265167655292649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7805541645686890207056865 5854156234265167655292649)
        ·
          refine ⟨4390617175698875741469487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5854156234265167655292649 4390617175698875741469487)
          ·
            refine ⟨6585925763548313612204231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4390617175698875741469487 6585925763548313612204231)
            ·
              refine ⟨9878888645322470418306347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6585925763548313612204231 9878888645322470418306347)
              ·
                refine ⟨14818332967983705627459521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9878888645322470418306347 14818332967983705627459521)
                ·
                  refine ⟨11113749725987779220594641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14818332967983705627459521 11113749725987779220594641)
                  ·
                    refine ⟨8335312294490834415445981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11113749725987779220594641 8335312294490834415445981)
                    ·
                      refine ⟨3125742110434062905792243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8335312294490834415445981 3125742110434062905792243)
                      ·
                        rfl

theorem cell23_6087361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_6087361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087361 prefixEnd_6087361 := by exact prefixLift 6087361
  have htrace : WordTrace (prefixWord ++ tailWord_6087361) baseStart_6087361 baseEnd_6087361 := by
    simpa [prefixWord, tailWord_6087361, baseEnd_6087361] using wordTrace_append hprefix tailTrace_6087361
  have hstable : (prefixWord ++ tailWord_6087361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087361).length < 2 ^ (prefixWord ++ tailWord_6087361).sum := by decide
  have hdescent : baseEnd_6087361 < baseStart_6087361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087374 : List Nat := [4, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3]
def baseStart_6087374 : Nat := 118140960795 + 6087374 * 2 ^ 59
def prefixEnd_6087374 : Nat := 4983230072969 + 3 ^ 40 * 6087374 * 2
def baseEnd_6087374 : Nat := 3125748785682571354929683

theorem tailTrace_6087374 : CollatzResearch.WordTrace tailWord_6087374 prefixEnd_6087374 3125748785682571354929683 := by
  unfold tailWord_6087374
  simp only [CollatzResearch.WordTrace]
  refine ⟨27753096231061389194285647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148016513232327409036190117 27753096231061389194285647)
  ·
    refine ⟨41629644346592083791428471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27753096231061389194285647 41629644346592083791428471)
    ·
      refine ⟨62444466519888125687142707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41629644346592083791428471 62444466519888125687142707)
      ·
        refine ⟨93666699779832188530714061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62444466519888125687142707 93666699779832188530714061)
        ·
          refine ⟨35125012417437070699017773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93666699779832188530714061 35125012417437070699017773)
          ·
            refine ⟨13171879656538901512131665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35125012417437070699017773 13171879656538901512131665)
            ·
              refine ⟨9878909742404176134098749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13171879656538901512131665 9878909742404176134098749)
              ·
                refine ⟨3704591153401566050287031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9878909742404176134098749 3704591153401566050287031)
                ·
                  refine ⟨5556886730102349075430547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3704591153401566050287031 5556886730102349075430547)
                  ·
                    refine ⟨8335330095153523613145821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5556886730102349075430547 8335330095153523613145821)
                    ·
                      refine ⟨3125748785682571354929683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8335330095153523613145821 3125748785682571354929683)
                      ·
                        rfl

theorem cell23_6087374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3].length) (baseStart_6087374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087374 prefixEnd_6087374 := by exact prefixLift 6087374
  have htrace : WordTrace (prefixWord ++ tailWord_6087374) baseStart_6087374 baseEnd_6087374 := by
    simpa [prefixWord, tailWord_6087374, baseEnd_6087374] using wordTrace_append hprefix tailTrace_6087374
  have hstable : (prefixWord ++ tailWord_6087374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087374).length < 2 ^ (prefixWord ++ tailWord_6087374).sum := by decide
  have hdescent : baseEnd_6087374 < baseStart_6087374 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087376 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 4]
def baseStart_6087376 : Nat := 118140960795 + 6087376 * 2 ^ 59
def prefixEnd_6087376 : Nat := 4983230072969 + 3 ^ 40 * 6087376 * 2
def baseEnd_6087376 : Nat := 3125749812643880347104673

theorem tailTrace_6087376 : CollatzResearch.WordTrace tailWord_6087376 prefixEnd_6087376 3125749812643880347104673 := by
  unfold tailWord_6087376
  simp only [CollatzResearch.WordTrace]
  refine ⟨111012421397241933947928991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148016561862989245263905321 111012421397241933947928991)
  ·
    refine ⟨166518632095862900921893487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111012421397241933947928991 166518632095862900921893487)
    ·
      refine ⟨249777948143794351382840231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166518632095862900921893487 249777948143794351382840231)
      ·
        refine ⟨374666922215691527074260347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249777948143794351382840231 374666922215691527074260347)
        ·
          refine ⟨562000383323537290611390521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374666922215691527074260347 562000383323537290611390521)
          ·
            refine ⟨421500287492652967958542891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 562000383323537290611390521 421500287492652967958542891)
            ·
              refine ⟨632250431238979451937814337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 421500287492652967958542891 632250431238979451937814337)
              ·
                refine ⟨474187823429234588953360753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 632250431238979451937814337 474187823429234588953360753)
                ·
                  refine ⟨355640867571925941715020565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 474187823429234588953360753 355640867571925941715020565)
                  ·
                    refine ⟨16670665667434028517891589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 355640867571925941715020565 16670665667434028517891589)
                    ·
                      refine ⟨3125749812643880347104673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16670665667434028517891589 3125749812643880347104673)
                      ·
                        rfl

theorem cell23_6087376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 4].length) (baseStart_6087376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087376 prefixEnd_6087376 := by exact prefixLift 6087376
  have htrace : WordTrace (prefixWord ++ tailWord_6087376) baseStart_6087376 baseEnd_6087376 := by
    simpa [prefixWord, tailWord_6087376, baseEnd_6087376] using wordTrace_append hprefix tailTrace_6087376
  have hstable : (prefixWord ++ tailWord_6087376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087376).length < 2 ^ (prefixWord ++ tailWord_6087376).sum := by decide
  have hdescent : baseEnd_6087376 < baseStart_6087376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087386 : List Nat := [3, 1, 1, 2, 2, 2, 12]
def baseStart_6087386 : Nat := 118140960795 + 6087386 * 2 ^ 59
def prefixEnd_6087386 : Nat := 4983230072969 + 3 ^ 40 * 6087386 * 2
def baseEnd_6087386 : Nat := 38589567252474386518267

theorem tailTrace_6087386 : CollatzResearch.WordTrace tailWord_6087386 prefixEnd_6087386 38589567252474386518267 := by
  unfold tailWord_6087386
  simp only [CollatzResearch.WordTrace]
  refine ⟨55506301881111909900930503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148016805016298426402481341 55506301881111909900930503)
  ·
    refine ⟨83259452821667864851395755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55506301881111909900930503 83259452821667864851395755)
    ·
      refine ⟨124889179232501797277093633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83259452821667864851395755 124889179232501797277093633)
      ·
        refine ⟨93666884424376347957820225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124889179232501797277093633 93666884424376347957820225)
        ·
          refine ⟨70250163318282260968365169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93666884424376347957820225 70250163318282260968365169)
          ·
            refine ⟨52687622488711695726273877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70250163318282260968365169 52687622488711695726273877)
            ·
              refine ⟨38589567252474386518267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 52687622488711695726273877 38589567252474386518267)
              ·
                rfl

theorem cell23_6087386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 12].length) (baseStart_6087386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087386 prefixEnd_6087386 := by exact prefixLift 6087386
  have htrace : WordTrace (prefixWord ++ tailWord_6087386) baseStart_6087386 baseEnd_6087386 := by
    simpa [prefixWord, tailWord_6087386, baseEnd_6087386] using wordTrace_append hprefix tailTrace_6087386
  have hstable : (prefixWord ++ tailWord_6087386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087386).length < 2 ^ (prefixWord ++ tailWord_6087386).sum := by decide
  have hdescent : baseEnd_6087386 < baseStart_6087386 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087397 : List Nat := [1, 3, 1, 4, 1, 2, 1, 3, 3, 2, 2]
def baseStart_6087397 : Nat := 118140960795 + 6087397 * 2 ^ 59
def prefixEnd_6087397 : Nat := 4983230072969 + 3 ^ 40 * 6087397 * 2
def baseEnd_6087397 : Nat := 3125760595737624764942077

theorem tailTrace_6087397 : CollatzResearch.WordTrace tailWord_6087397 prefixEnd_6087397 3125760595737624764942077 := by
  unfold tailWord_6087397
  simp only [CollatzResearch.WordTrace]
  refine ⟨222025608727407788482372445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148017072484938525654914963 222025608727407788482372445)
  ·
    refine ⟨83259603272777920680889667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222025608727407788482372445 83259603272777920680889667)
    ·
      refine ⟨124889404909166881021334501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83259603272777920680889667 124889404909166881021334501)
      ·
        refine ⟨23416763420468790191500219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124889404909166881021334501 23416763420468790191500219)
        ·
          refine ⟨35125145130703185287250329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23416763420468790191500219 35125145130703185287250329)
          ·
            refine ⟨26343858848027388965437747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35125145130703185287250329 26343858848027388965437747)
            ·
              refine ⟨39515788272041083448156621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26343858848027388965437747 39515788272041083448156621)
              ·
                refine ⟨14818420602015406293058733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39515788272041083448156621 14818420602015406293058733)
                ·
                  refine ⟨5556907725755777359897025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14818420602015406293058733 5556907725755777359897025)
                  ·
                    refine ⟨4167680794316833019922769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5556907725755777359897025 4167680794316833019922769)
                    ·
                      refine ⟨3125760595737624764942077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4167680794316833019922769 3125760595737624764942077)
                      ·
                        rfl

theorem cell23_6087397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_6087397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087397 prefixEnd_6087397 := by exact prefixLift 6087397
  have htrace : WordTrace (prefixWord ++ tailWord_6087397) baseStart_6087397 baseEnd_6087397 := by
    simpa [prefixWord, tailWord_6087397, baseEnd_6087397] using wordTrace_append hprefix tailTrace_6087397
  have hstable : (prefixWord ++ tailWord_6087397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087397).length < 2 ^ (prefixWord ++ tailWord_6087397).sum := by decide
  have hdescent : baseEnd_6087397 < baseStart_6087397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087400 : List Nat := [2, 1, 4, 1, 4, 1, 1, 2, 1, 1, 5]
def baseStart_6087400 : Nat := 118140960795 + 6087400 * 2 ^ 59
def prefixEnd_6087400 : Nat := 4983230072969 + 3 ^ 40 * 6087400 * 2
def baseEnd_6087400 : Nat := 3125762136179588253204563

theorem tailTrace_6087400 : CollatzResearch.WordTrace tailWord_6087400 prefixEnd_6087400 3125762136179588253204563 := by
  unfold tailWord_6087400
  simp only [CollatzResearch.WordTrace]
  refine ⟨111012859073198459997365827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148017145430931279996487769 111012859073198459997365827)
  ·
    refine ⟨166519288609797689996048741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111012859073198459997365827 166519288609797689996048741)
    ·
      refine ⟨31222366614337066874259139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166519288609797689996048741 31222366614337066874259139)
      ·
        refine ⟨46833549921505600311388709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31222366614337066874259139 46833549921505600311388709)
        ·
          refine ⟨8781290610282300058385383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46833549921505600311388709 8781290610282300058385383)
          ·
            refine ⟨13171935915423450087578075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8781290610282300058385383 13171935915423450087578075)
            ·
              refine ⟨19757903873135175131367113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13171935915423450087578075 19757903873135175131367113)
              ·
                refine ⟨14818427904851381348525335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19757903873135175131367113 14818427904851381348525335)
                ·
                  refine ⟨22227641857277072022788003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14818427904851381348525335 22227641857277072022788003)
                  ·
                    refine ⟨33341462785915608034182005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22227641857277072022788003 33341462785915608034182005)
                    ·
                      refine ⟨3125762136179588253204563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33341462785915608034182005 3125762136179588253204563)
                      ·
                        rfl

theorem cell23_6087400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_6087400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087400 prefixEnd_6087400 := by exact prefixLift 6087400
  have htrace : WordTrace (prefixWord ++ tailWord_6087400) baseStart_6087400 baseEnd_6087400 := by
    simpa [prefixWord, tailWord_6087400, baseEnd_6087400] using wordTrace_append hprefix tailTrace_6087400
  have hstable : (prefixWord ++ tailWord_6087400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087400).length < 2 ^ (prefixWord ++ tailWord_6087400).sum := by decide
  have hdescent : baseEnd_6087400 < baseStart_6087400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087407 : List Nat := [1, 1, 2, 1, 5, 3, 3, 1, 2, 4]
def baseStart_6087407 : Nat := 118140960795 + 6087407 * 2 ^ 59
def prefixEnd_6087407 : Nat := 4983230072969 + 3 ^ 40 * 6087407 * 2
def baseEnd_6087407 : Nat := 1041921910181389908605677

theorem tailTrace_6087407 : CollatzResearch.WordTrace tailWord_6087407 prefixEnd_6087407 1041921910181389908605677 := by
  unfold tailWord_6087407
  simp only [CollatzResearch.WordTrace]
  refine ⟨222025973457371560190236475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148017315638247706793490983 222025973457371560190236475)
  ·
    refine ⟨333038960186057340285354713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222025973457371560190236475 333038960186057340285354713)
    ·
      refine ⟨249779220139543005214016035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333038960186057340285354713 249779220139543005214016035)
      ·
        refine ⟨374668830209314507821024053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249779220139543005214016035 374668830209314507821024053)
        ·
          refine ⟨35125202832123235108221005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 374668830209314507821024053 35125202832123235108221005)
          ·
            refine ⟨13171951062046213165582877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35125202832123235108221005 13171951062046213165582877)
            ·
              refine ⟨4939481648267329937093579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13171951062046213165582877 4939481648267329937093579)
              ·
                refine ⟨7409222472400994905640369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4939481648267329937093579 7409222472400994905640369)
                ·
                  refine ⟨5556916854300746179230277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7409222472400994905640369 5556916854300746179230277)
                  ·
                    refine ⟨1041921910181389908605677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5556916854300746179230277 1041921910181389908605677)
                    ·
                      rfl

theorem cell23_6087407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 1, 2, 4].length) (baseStart_6087407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087407 prefixEnd_6087407 := by exact prefixLift 6087407
  have htrace : WordTrace (prefixWord ++ tailWord_6087407) baseStart_6087407 baseEnd_6087407 := by
    simpa [prefixWord, tailWord_6087407, baseEnd_6087407] using wordTrace_append hprefix tailTrace_6087407
  have hstable : (prefixWord ++ tailWord_6087407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087407).length < 2 ^ (prefixWord ++ tailWord_6087407).sum := by decide
  have hdescent : baseEnd_6087407 < baseStart_6087407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087410 : List Nat := [3, 2, 1, 3, 1, 2, 3, 1, 1, 2, 4]
def baseStart_6087410 : Nat := 118140960795 + 6087410 * 2 ^ 59
def prefixEnd_6087410 : Nat := 4983230072969 + 3 ^ 40 * 6087410 * 2
def baseEnd_6087410 : Nat := 3125767270986133214079517

theorem tailTrace_6087410 : CollatzResearch.WordTrace tailWord_6087410 prefixEnd_6087410 3125767270986133214079517 := by
  unfold tailWord_6087410
  simp only [CollatzResearch.WordTrace]
  refine ⟨55506520719090172925648921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148017388584240461135063789 55506520719090172925648921)
  ·
    refine ⟨41629890539317629694236691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55506520719090172925648921 41629890539317629694236691)
    ·
      refine ⟨62444835808976444541355037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41629890539317629694236691 62444835808976444541355037)
      ·
        refine ⟨23416813428366166703008139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62444835808976444541355037 23416813428366166703008139)
        ·
          refine ⟨35125220142549250054512209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23416813428366166703008139 35125220142549250054512209)
          ·
            refine ⟨26343915106911937540884157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35125220142549250054512209 26343915106911937540884157)
            ·
              refine ⟨9878968165091976577831559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26343915106911937540884157 9878968165091976577831559)
              ·
                refine ⟨14818452247637964866747339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9878968165091976577831559 14818452247637964866747339)
                ·
                  refine ⟨22227678371456947300121009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14818452247637964866747339 22227678371456947300121009)
                  ·
                    refine ⟨16670758778592710475090757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22227678371456947300121009 16670758778592710475090757)
                    ·
                      refine ⟨3125767270986133214079517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16670758778592710475090757 3125767270986133214079517)
                      ·
                        rfl

theorem cell23_6087410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_6087410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087410 prefixEnd_6087410 := by exact prefixLift 6087410
  have htrace : WordTrace (prefixWord ++ tailWord_6087410) baseStart_6087410 baseEnd_6087410 := by
    simpa [prefixWord, tailWord_6087410, baseEnd_6087410] using wordTrace_append hprefix tailTrace_6087410
  have hstable : (prefixWord ++ tailWord_6087410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087410).length < 2 ^ (prefixWord ++ tailWord_6087410).sum := by decide
  have hdescent : baseEnd_6087410 < baseStart_6087410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087420 : List Nat := [2, 2, 2, 1, 3, 4, 2, 7]
def baseStart_6087420 : Nat := 118140960795 + 6087420 * 2 ^ 59
def prefixEnd_6087420 : Nat := 4983230072969 + 3 ^ 40 * 6087420 * 2
def baseEnd_6087420 : Nat := 115769348362691784257573

theorem tailTrace_6087420 : CollatzResearch.WordTrace tailWord_6087420 prefixEnd_6087420 115769348362691784257573 := by
  unfold tailWord_6087420
  simp only [CollatzResearch.WordTrace]
  refine ⟨111013223803162231705229857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148017631737549642273639809 111013223803162231705229857)
  ·
    refine ⟨83259917852371673778922393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111013223803162231705229857 83259917852371673778922393)
    ·
      refine ⟨62444938389278755334191795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83259917852371673778922393 62444938389278755334191795)
      ·
        refine ⟨93667407583918133001287693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62444938389278755334191795 93667407583918133001287693)
        ·
          refine ⟨35125277843969299875482885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93667407583918133001287693 35125277843969299875482885)
          ·
            refine ⟨6585989595744243726653041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35125277843969299875482885 6585989595744243726653041)
            ·
              refine ⟨4939492196808182794989781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6585989595744243726653041 4939492196808182794989781)
              ·
                refine ⟨115769348362691784257573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4939492196808182794989781 115769348362691784257573)
                ·
                  rfl

theorem cell23_6087420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 7].length) (baseStart_6087420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087420 prefixEnd_6087420 := by exact prefixLift 6087420
  have htrace : WordTrace (prefixWord ++ tailWord_6087420) baseStart_6087420 baseEnd_6087420 := by
    simpa [prefixWord, tailWord_6087420, baseEnd_6087420] using wordTrace_append hprefix tailTrace_6087420
  have hstable : (prefixWord ++ tailWord_6087420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087420).length < 2 ^ (prefixWord ++ tailWord_6087420).sum := by decide
  have hdescent : baseEnd_6087420 < baseStart_6087420 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087431 : List Nat := [1, 1, 4, 4, 1, 1, 3, 3, 1, 2, 2]
def baseStart_6087431 : Nat := 118140960795 + 6087431 * 2 ^ 59
def prefixEnd_6087431 : Nat := 4983230072969 + 3 ^ 40 * 6087431 * 2
def baseEnd_6087431 : Nat := 3125778054079877631916921

theorem tailTrace_6087431 : CollatzResearch.WordTrace tailWord_6087431 prefixEnd_6087431 3125778054079877631916921 := by
  unfold tailWord_6087431
  simp only [CollatzResearch.WordTrace]
  refine ⟨222026848809284612289110147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148017899206189741526073431 222026848809284612289110147)
  ·
    refine ⟨333040273213926918433665221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222026848809284612289110147 333040273213926918433665221)
    ·
      refine ⟨62445051227611297206312229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 333040273213926918433665221 62445051227611297206312229)
      ·
        refine ⟨11708447105177118226183543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62445051227611297206312229 11708447105177118226183543)
        ·
          refine ⟨17562670657765677339275315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11708447105177118226183543 17562670657765677339275315)
          ·
            refine ⟨26344005986648516008912973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17562670657765677339275315 26344005986648516008912973)
            ·
              refine ⟨9879002244993193503342365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26344005986648516008912973 9879002244993193503342365)
              ·
                refine ⟨3704625841872447563753387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9879002244993193503342365 3704625841872447563753387)
                ·
                  refine ⟨5556938762808671345630081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3704625841872447563753387 5556938762808671345630081)
                  ·
                    refine ⟨4167704072106503509222561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5556938762808671345630081 4167704072106503509222561)
                    ·
                      refine ⟨3125778054079877631916921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4167704072106503509222561 3125778054079877631916921)
                      ·
                        rfl

theorem cell23_6087431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_6087431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087431 prefixEnd_6087431 := by exact prefixLift 6087431
  have htrace : WordTrace (prefixWord ++ tailWord_6087431) baseStart_6087431 baseEnd_6087431 := by
    simpa [prefixWord, tailWord_6087431, baseEnd_6087431] using wordTrace_append hprefix tailTrace_6087431
  have hstable : (prefixWord ++ tailWord_6087431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087431).length < 2 ^ (prefixWord ++ tailWord_6087431).sum := by decide
  have hdescent : baseEnd_6087431 < baseStart_6087431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087473 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 4, 1, 5]
def baseStart_6087473 : Nat := 118140960795 + 6087473 * 2 ^ 59
def prefixEnd_6087473 : Nat := 4983230072969 + 3 ^ 40 * 6087473 * 2
def baseEnd_6087473 : Nat := 3125799620267366467591727

theorem tailTrace_6087473 : CollatzResearch.WordTrace tailWord_6087473 prefixEnd_6087473 3125799620267366467591727 := by
  unfold tailWord_6087473
  simp only [CollatzResearch.WordTrace]
  refine ⟨222028380675132453462139073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148018920450088302308092715 222028380675132453462139073)
  ·
    refine ⟨166521285506349340096604305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222028380675132453462139073 166521285506349340096604305)
    ·
      refine ⟨124890964129762005072453229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166521285506349340096604305 124890964129762005072453229)
      ·
        refine ⟨46834111548660751902169961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124890964129762005072453229 46834111548660751902169961)
        ·
          refine ⟨35125583661495563926627471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46834111548660751902169961 35125583661495563926627471)
          ·
            refine ⟨52688375492243345889941207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35125583661495563926627471 52688375492243345889941207)
            ·
              refine ⟨79032563238365018834911811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52688375492243345889941207 79032563238365018834911811)
              ·
                refine ⟨118548844857547528252367717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79032563238365018834911811 118548844857547528252367717)
                ·
                  refine ⟨22227908410790161547318947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 118548844857547528252367717 22227908410790161547318947)
                  ·
                    refine ⟨33341862616185242320978421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22227908410790161547318947 33341862616185242320978421)
                    ·
                      refine ⟨3125799620267366467591727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33341862616185242320978421 3125799620267366467591727)
                      ·
                        rfl

theorem cell23_6087473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_6087473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087473 prefixEnd_6087473 := by exact prefixLift 6087473
  have htrace : WordTrace (prefixWord ++ tailWord_6087473) baseStart_6087473 baseEnd_6087473 := by
    simpa [prefixWord, tailWord_6087473, baseEnd_6087473] using wordTrace_append hprefix tailTrace_6087473
  have hstable : (prefixWord ++ tailWord_6087473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087473).length < 2 ^ (prefixWord ++ tailWord_6087473).sum := by decide
  have hdescent : baseEnd_6087473 < baseStart_6087473 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087487 : List Nat := [1, 1, 2, 2, 5, 2, 1, 2, 1, 4, 2]
def baseStart_6087487 : Nat := 118140960795 + 6087487 * 2 ^ 59
def prefixEnd_6087487 : Nat := 4983230072969 + 3 ^ 40 * 6087487 * 2
def baseEnd_6087487 : Nat := 3125806808996529412816663

theorem tailTrace_6087487 : CollatzResearch.WordTrace tailWord_6087487 prefixEnd_6087487 3125806808996529412816663 := by
  unfold tailWord_6087487
  simp only [CollatzResearch.WordTrace]
  refine ⟨222028891297081733853148715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148019260864721155902099143 222028891297081733853148715)
  ·
    refine ⟨333043336945622600779723073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222028891297081733853148715 333043336945622600779723073)
    ·
      refine ⟨249782502709216950584792305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333043336945622600779723073 249782502709216950584792305)
      ·
        refine ⟨187336877031912712938594229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249782502709216950584792305 187336877031912712938594229)
        ·
          refine ⟨17562832221741816837993209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 187336877031912712938594229 17562832221741816837993209)
          ·
            refine ⟨13172124166306362628494907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17562832221741816837993209 13172124166306362628494907)
            ·
              refine ⟨19758186249459543942742361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13172124166306362628494907 19758186249459543942742361)
              ·
                refine ⟨14818639687094657957056771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19758186249459543942742361 14818639687094657957056771)
                ·
                  refine ⟨22227959530641986935585157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14818639687094657957056771 22227959530641986935585157)
                  ·
                    refine ⟨4167742411995372550422217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22227959530641986935585157 4167742411995372550422217)
                    ·
                      refine ⟨3125806808996529412816663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4167742411995372550422217 3125806808996529412816663)
                      ·
                        rfl

theorem cell23_6087487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 4, 2].length) (baseStart_6087487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087487 prefixEnd_6087487 := by exact prefixLift 6087487
  have htrace : WordTrace (prefixWord ++ tailWord_6087487) baseStart_6087487 baseEnd_6087487 := by
    simpa [prefixWord, tailWord_6087487, baseEnd_6087487] using wordTrace_append hprefix tailTrace_6087487
  have hstable : (prefixWord ++ tailWord_6087487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087487).length < 2 ^ (prefixWord ++ tailWord_6087487).sum := by decide
  have hdescent : baseEnd_6087487 < baseStart_6087487 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087503 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 5, 5, 3]
def baseStart_6087503 : Nat := 118140960795 + 6087503 * 2 ^ 59
def prefixEnd_6087503 : Nat := 4983230072969 + 3 ^ 40 * 6087503 * 2
def baseEnd_6087503 : Nat := 3125815024687001350216589

theorem tailTrace_6087503 : CollatzResearch.WordTrace tailWord_6087503 prefixEnd_6087503 3125815024687001350216589 := by
  unfold tailWord_6087503
  simp only [CollatzResearch.WordTrace]
  refine ⟨222029474865023768585731163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148019649910015845723820775 222029474865023768585731163)
  ·
    refine ⟨333044212297535652878596745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222029474865023768585731163 333044212297535652878596745)
    ·
      refine ⟨249783159223151739658947559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333044212297535652878596745 249783159223151739658947559)
      ·
        refine ⟨374674738834727609488421339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249783159223151739658947559 374674738834727609488421339)
        ·
          refine ⟨562012108252091414232632009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374674738834727609488421339 562012108252091414232632009)
          ·
            refine ⟨421509081189068560674474007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 562012108252091414232632009 421509081189068560674474007)
            ·
              refine ⟨632263621783602841011711011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 421509081189068560674474007 632263621783602841011711011)
              ·
                refine ⟨948395432675404261517566517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 632263621783602841011711011 948395432675404261517566517)
                ·
                  refine ⟨88912071813319149517271861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 948395432675404261517566517 88912071813319149517271861)
                  ·
                    refine ⟨8335506732498670267244237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88912071813319149517271861 8335506732498670267244237)
                    ·
                      refine ⟨3125815024687001350216589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8335506732498670267244237 3125815024687001350216589)
                      ·
                        rfl

theorem cell23_6087503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 5, 3].length) (baseStart_6087503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087503 prefixEnd_6087503 := by exact prefixLift 6087503
  have htrace : WordTrace (prefixWord ++ tailWord_6087503) baseStart_6087503 baseEnd_6087503 := by
    simpa [prefixWord, tailWord_6087503, baseEnd_6087503] using wordTrace_append hprefix tailTrace_6087503
  have hstable : (prefixWord ++ tailWord_6087503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087503).length < 2 ^ (prefixWord ++ tailWord_6087503).sum := by decide
  have hdescent : baseEnd_6087503 < baseStart_6087503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087520 : List Nat := [2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 3]
def baseStart_6087520 : Nat := 118140960795 + 6087520 * 2 ^ 59
def prefixEnd_6087520 : Nat := 4983230072969 + 3 ^ 40 * 6087520 * 2
def baseEnd_6087520 : Nat := 3125823753858127783704011

theorem tailTrace_6087520 : CollatzResearch.WordTrace tailWord_6087520 prefixEnd_6087520 3125823753858127783704011 := by
  unfold tailWord_6087520
  simp only [CollatzResearch.WordTrace]
  refine ⟨111015047452981090244550007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148020063270641453659400009 111015047452981090244550007)
  ·
    refine ⟨166522571179471635366825011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111015047452981090244550007 166522571179471635366825011)
    ·
      refine ⟨249783856769207453050237517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166522571179471635366825011 249783856769207453050237517)
      ·
        refine ⟨93668946288452794893839069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249783856769207453050237517 93668946288452794893839069)
        ·
          refine ⟨35125854858169798085189651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93668946288452794893839069 35125854858169798085189651)
          ·
            refine ⟨52688782287254697127784477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35125854858169798085189651 52688782287254697127784477)
            ·
              refine ⟨19758293357720511422919179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52688782287254697127784477 19758293357720511422919179)
              ·
                refine ⟨29637440036580767134378769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19758293357720511422919179 29637440036580767134378769)
                ·
                  refine ⟨22228080027435575350784077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29637440036580767134378769 22228080027435575350784077)
                  ·
                    refine ⟨8335530010288340756544029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22228080027435575350784077 8335530010288340756544029)
                    ·
                      refine ⟨3125823753858127783704011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8335530010288340756544029 3125823753858127783704011)
                      ·
                        rfl

theorem cell23_6087520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 2, 3, 3].length) (baseStart_6087520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087520 prefixEnd_6087520 := by exact prefixLift 6087520
  have htrace : WordTrace (prefixWord ++ tailWord_6087520) baseStart_6087520 baseEnd_6087520 := by
    simpa [prefixWord, tailWord_6087520, baseEnd_6087520] using wordTrace_append hprefix tailTrace_6087520
  have hstable : (prefixWord ++ tailWord_6087520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087520).length < 2 ^ (prefixWord ++ tailWord_6087520).sum := by decide
  have hdescent : baseEnd_6087520 < baseStart_6087520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087563 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 5]
def baseStart_6087563 : Nat := 118140960795 + 6087563 * 2 ^ 59
def prefixEnd_6087563 : Nat := 4983230072969 + 3 ^ 40 * 6087563 * 2
def baseEnd_6087563 : Nat := 3125845833526271115466313

theorem tailTrace_6087563 : CollatzResearch.WordTrace tailWord_6087563 prefixEnd_6087563 3125845833526271115466313 := by
  unfold tailWord_6087563
  simp only [CollatzResearch.WordTrace]
  refine ⟨222031663244806398832915343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148021108829870932555276895 222031663244806398832915343)
  ·
    refine ⟨333047494867209598249373015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222031663244806398832915343 333047494867209598249373015)
    ·
      refine ⟨499571242300814397374059523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333047494867209598249373015 499571242300814397374059523)
      ·
        refine ⟨749356863451221596061089285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 499571242300814397374059523 749356863451221596061089285)
        ·
          refine ⟨140504411897104049261454241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 749356863451221596061089285 140504411897104049261454241)
          ·
            refine ⟨105378308922828036946090681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140504411897104049261454241 105378308922828036946090681)
            ·
              refine ⟨79033731692121027709568011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105378308922828036946090681 79033731692121027709568011)
              ·
                refine ⟨118550597538181541564352017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79033731692121027709568011 118550597538181541564352017)
                ·
                  refine ⟨88912948153636156173264013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118550597538181541564352017 88912948153636156173264013)
                  ·
                    refine ⟨33342355557613558564974005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88912948153636156173264013 33342355557613558564974005)
                    ·
                      refine ⟨3125845833526271115466313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33342355557613558564974005 3125845833526271115466313)
                      ·
                        rfl

theorem cell23_6087563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 3, 5].length) (baseStart_6087563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087563 prefixEnd_6087563 := by exact prefixLift 6087563
  have htrace : WordTrace (prefixWord ++ tailWord_6087563) baseStart_6087563 baseEnd_6087563 := by
    simpa [prefixWord, tailWord_6087563, baseEnd_6087563] using wordTrace_append hprefix tailTrace_6087563
  have hstable : (prefixWord ++ tailWord_6087563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087563).length < 2 ^ (prefixWord ++ tailWord_6087563).sum := by decide
  have hdescent : baseEnd_6087563 < baseStart_6087563 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087574 : List Nat := [5, 3, 1, 1, 1, 1, 1, 2, 1, 7]
def baseStart_6087574 : Nat := 118140960795 + 6087574 * 2 ^ 59
def prefixEnd_6087574 : Nat := 4983230072969 + 3 ^ 40 * 6087574 * 2
def baseEnd_6087574 : Nat := 1041950493937823524142921

theorem tailTrace_6087574 : CollatzResearch.WordTrace tailWord_6087574 prefixEnd_6087574 1041950493937823524142921 := by
  unfold tailWord_6087574
  simp only [CollatzResearch.WordTrace]
  refine ⟨13877004027985409231972861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148021376298511031807710517 13877004027985409231972861)
  ·
    refine ⟨5203876510494528461989823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13877004027985409231972861 5203876510494528461989823)
    ·
      refine ⟨7805814765741792692984735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5203876510494528461989823 7805814765741792692984735)
      ·
        refine ⟨11708722148612689039477103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7805814765741792692984735 11708722148612689039477103)
        ·
          refine ⟨17563083222919033559215655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11708722148612689039477103 17563083222919033559215655)
          ·
            refine ⟨26344624834378550338823483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17563083222919033559215655 26344624834378550338823483)
            ·
              refine ⟨39516937251567825508235225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26344624834378550338823483 39516937251567825508235225)
              ·
                refine ⟨29637702938675869131176419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39516937251567825508235225 29637702938675869131176419)
                ·
                  refine ⟨44456554408013803696764629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29637702938675869131176419 44456554408013803696764629)
                  ·
                    refine ⟨1041950493937823524142921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44456554408013803696764629 1041950493937823524142921)
                    ·
                      rfl

theorem cell23_6087574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_6087574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087574 prefixEnd_6087574 := by exact prefixLift 6087574
  have htrace : WordTrace (prefixWord ++ tailWord_6087574) baseStart_6087574 baseEnd_6087574 := by
    simpa [prefixWord, tailWord_6087574, baseEnd_6087574] using wordTrace_append hprefix tailTrace_6087574
  have hstable : (prefixWord ++ tailWord_6087574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087574).length < 2 ^ (prefixWord ++ tailWord_6087574).sum := by decide
  have hdescent : baseEnd_6087574 < baseStart_6087574 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087603 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 8]
def baseStart_6087603 : Nat := 118140960795 + 6087603 * 2 ^ 59
def prefixEnd_6087603 : Nat := 4983230072969 + 3 ^ 40 * 6087603 * 2
def baseEnd_6087603 : Nat := 3125866372752450958966129

theorem tailTrace_6087603 : CollatzResearch.WordTrace tailWord_6087603 prefixEnd_6087603 3125866372752450958966129 := by
  unfold tailWord_6087603
  simp only [CollatzResearch.WordTrace]
  refine ⟨222033122164661485664371463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148022081443107657109580975 222033122164661485664371463)
  ·
    refine ⟨333049683246992228496557195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222033122164661485664371463 333049683246992228496557195)
    ·
      refine ⟨499574524870488342744835793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333049683246992228496557195 499574524870488342744835793)
      ·
        refine ⟨374680893652866257058626845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 499574524870488342744835793 374680893652866257058626845)
        ·
          refine ⟨140505335119824846396985067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 374680893652866257058626845 140505335119824846396985067)
          ·
            refine ⟨210758002679737269595477601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140505335119824846396985067 210758002679737269595477601)
            ·
              refine ⟨158068502009802952196608201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210758002679737269595477601 158068502009802952196608201)
              ·
                refine ⟨118551376507352214147456151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158068502009802952196608201 118551376507352214147456151)
                ·
                  refine ⟨177827064761028321221184227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118551376507352214147456151 177827064761028321221184227)
                  ·
                    refine ⟨266740597141542481831776341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 177827064761028321221184227 266740597141542481831776341)
                    ·
                      refine ⟨3125866372752450958966129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 266740597141542481831776341 3125866372752450958966129)
                      ·
                        rfl

theorem cell23_6087603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 8].length) (baseStart_6087603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087603 prefixEnd_6087603 := by exact prefixLift 6087603
  have htrace : WordTrace (prefixWord ++ tailWord_6087603) baseStart_6087603 baseEnd_6087603 := by
    simpa [prefixWord, tailWord_6087603, baseEnd_6087603] using wordTrace_append hprefix tailTrace_6087603
  have hstable : (prefixWord ++ tailWord_6087603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087603).length < 2 ^ (prefixWord ++ tailWord_6087603).sum := by decide
  have hdescent : baseEnd_6087603 < baseStart_6087603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087634 : List Nat := [3, 2, 2, 3, 1, 1, 4, 1, 6]
def baseStart_6087634 : Nat := 118140960795 + 6087634 * 2 ^ 59
def prefixEnd_6087634 : Nat := 4983230072969 + 3 ^ 40 * 6087634 * 2
def baseEnd_6087634 : Nat := 347320254516971148630943

theorem tailTrace_6087634 : CollatzResearch.WordTrace tailWord_6087634 prefixEnd_6087634 347320254516971148630943 := by
  unfold tailWord_6087634
  simp only [CollatzResearch.WordTrace]
  refine ⟨55508563206887294489687489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148022835218366118639166637 55508563206887294489687489)
  ·
    refine ⟨41631422405165470867265617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55508563206887294489687489 41631422405165470867265617)
    ·
      refine ⟨31223566803874103150449213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41631422405165470867265617 31223566803874103150449213)
      ·
        refine ⟨11708837551452788681418455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31223566803874103150449213 11708837551452788681418455)
        ·
          refine ⟨17563256327179183022127683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11708837551452788681418455 17563256327179183022127683)
          ·
            refine ⟨26344884490768774533191525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17563256327179183022127683 26344884490768774533191525)
            ·
              refine ⟨4939665842019145224973411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26344884490768774533191525 4939665842019145224973411)
              ·
                refine ⟨7409498763028717837460117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4939665842019145224973411 7409498763028717837460117)
                ·
                  refine ⟨347320254516971148630943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7409498763028717837460117 347320254516971148630943)
                  ·
                    rfl

theorem cell23_6087634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 6].length) (baseStart_6087634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087634 prefixEnd_6087634 := by exact prefixLift 6087634
  have htrace : WordTrace (prefixWord ++ tailWord_6087634) baseStart_6087634 baseEnd_6087634 := by
    simpa [prefixWord, tailWord_6087634, baseEnd_6087634] using wordTrace_append hprefix tailTrace_6087634
  have hstable : (prefixWord ++ tailWord_6087634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087634).length < 2 ^ (prefixWord ++ tailWord_6087634).sum := by decide
  have hdescent : baseEnd_6087634 < baseStart_6087634 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087647 : List Nat := [1, 1, 2, 3, 5, 1, 1, 1, 3, 5]
def baseStart_6087647 : Nat := 118140960795 + 6087647 * 2 ^ 59
def prefixEnd_6087647 : Nat := 4983230072969 + 3 ^ 40 * 6087647 * 2
def baseEnd_6087647 : Nat := 1041962988633749595605309

theorem tailTrace_6087647 : CollatzResearch.WordTrace tailWord_6087647 prefixEnd_6087647 1041962988633749595605309 := by
  unfold tailWord_6087647
  simp only [CollatzResearch.WordTrace]
  refine ⟨222034726976502081178973195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148023151317668054119315463 222034726976502081178973195)
  ·
    refine ⟨333052090464753121768459793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222034726976502081178973195 333052090464753121768459793)
    ·
      refine ⟨249789067848564841326344845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333052090464753121768459793 249789067848564841326344845)
      ·
        refine ⟨93670900443211815497379317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249789067848564841326344845 93670900443211815497379317)
        ·
          refine ⟨8781646916551107702879311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93670900443211815497379317 8781646916551107702879311)
          ·
            refine ⟨13172470374826661554318967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8781646916551107702879311 13172470374826661554318967)
            ·
              refine ⟨19758705562239992331478451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13172470374826661554318967 19758705562239992331478451)
              ·
                refine ⟨29638058343359988497217677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19758705562239992331478451 29638058343359988497217677)
                ·
                  refine ⟨11114271878759995686456629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29638058343359988497217677 11114271878759995686456629)
                  ·
                    refine ⟨1041962988633749595605309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11114271878759995686456629 1041962988633749595605309)
                    ·
                      rfl

theorem cell23_6087647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 3, 5].length) (baseStart_6087647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087647 prefixEnd_6087647 := by exact prefixLift 6087647
  have htrace : WordTrace (prefixWord ++ tailWord_6087647) baseStart_6087647 baseEnd_6087647 := by
    simpa [prefixWord, tailWord_6087647, baseEnd_6087647] using wordTrace_append hprefix tailTrace_6087647
  have hstable : (prefixWord ++ tailWord_6087647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087647).length < 2 ^ (prefixWord ++ tailWord_6087647).sum := by decide
  have hdescent : baseEnd_6087647 < baseStart_6087647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087687 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 5, 2, 3]
def baseStart_6087687 : Nat := 118140960795 + 6087687 * 2 ^ 59
def prefixEnd_6087687 : Nat := 4983230072969 + 3 ^ 40 * 6087687 * 2
def baseEnd_6087687 : Nat := 3125909505127428630315743

theorem tailTrace_6087687 : CollatzResearch.WordTrace tailWord_6087687 prefixEnd_6087687 3125909505127428630315743 := by
  unfold tailWord_6087687
  simp only [CollatzResearch.WordTrace]
  refine ⟨222036185896357168010429315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148024123930904778673619543 222036185896357168010429315)
  ·
    refine ⟨333054278844535752015643973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222036185896357168010429315 333054278844535752015643973)
    ·
      refine ⟨62447677283350453502933245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 333054278844535752015643973 62447677283350453502933245)
      ·
        refine ⟨23417878981256420063599967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62447677283350453502933245 23417878981256420063599967)
        ·
          refine ⟨35126818471884630095399951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23417878981256420063599967 35126818471884630095399951)
          ·
            refine ⟨52690227707826945143099927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35126818471884630095399951 52690227707826945143099927)
            ·
              refine ⟨79035341561740417714649891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52690227707826945143099927 79035341561740417714649891)
              ·
                refine ⟨118553012342610626571974837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79035341561740417714649891 118553012342610626571974837)
                ·
                  refine ⟨11114344907119746241122641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 118553012342610626571974837 11114344907119746241122641)
                  ·
                    refine ⟨8335758680339809680841981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11114344907119746241122641 8335758680339809680841981)
                    ·
                      refine ⟨3125909505127428630315743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8335758680339809680841981 3125909505127428630315743)
                      ·
                        rfl

theorem cell23_6087687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_6087687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087687 prefixEnd_6087687 := by exact prefixLift 6087687
  have htrace : WordTrace (prefixWord ++ tailWord_6087687) baseStart_6087687 baseEnd_6087687 := by
    simpa [prefixWord, tailWord_6087687, baseEnd_6087687] using wordTrace_append hprefix tailTrace_6087687
  have hstable : (prefixWord ++ tailWord_6087687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087687).length < 2 ^ (prefixWord ++ tailWord_6087687).sum := by decide
  have hdescent : baseEnd_6087687 < baseStart_6087687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087694 : List Nat := [4, 1, 1, 2, 2, 2, 2, 3, 2, 4]
def baseStart_6087694 : Nat := 118140960795 + 6087694 * 2 ^ 59
def prefixEnd_6087694 : Nat := 4983230072969 + 3 ^ 40 * 6087694 * 2
def baseEnd_6087694 : Nat := 1041971033164003367642737

theorem tailTrace_6087694 : CollatzResearch.WordTrace tailWord_6087694 prefixEnd_6087694 1041971033164003367642737 := by
  unfold tailWord_6087694
  simp only [CollatzResearch.WordTrace]
  refine ⟨27754555150916476025741767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148024294138221205470622757 27754555150916476025741767)
  ·
    refine ⟨41631832726374714038612651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27754555150916476025741767 41631832726374714038612651)
    ·
      refine ⟨62447749089562071057918977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41631832726374714038612651 62447749089562071057918977)
      ·
        refine ⟨46835811817171553293439233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62447749089562071057918977 46835811817171553293439233)
        ·
          refine ⟨35126858862878664970079425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46835811817171553293439233 35126858862878664970079425)
          ·
            refine ⟨26345144147158998727559569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35126858862878664970079425 26345144147158998727559569)
            ·
              refine ⟨19758858110369249045669677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26345144147158998727559569 19758858110369249045669677)
              ·
                refine ⟨7409571791388468392126129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19758858110369249045669677 7409571791388468392126129)
                ·
                  refine ⟨5557178843541351294094597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7409571791388468392126129 5557178843541351294094597)
                  ·
                    refine ⟨1041971033164003367642737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5557178843541351294094597 1041971033164003367642737)
                    ·
                      rfl

theorem cell23_6087694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 3, 2, 4].length) (baseStart_6087694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087694 prefixEnd_6087694 := by exact prefixLift 6087694
  have htrace : WordTrace (prefixWord ++ tailWord_6087694) baseStart_6087694 baseEnd_6087694 := by
    simpa [prefixWord, tailWord_6087694, baseEnd_6087694] using wordTrace_append hprefix tailTrace_6087694
  have hstable : (prefixWord ++ tailWord_6087694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087694).length < 2 ^ (prefixWord ++ tailWord_6087694).sum := by decide
  have hdescent : baseEnd_6087694 < baseStart_6087694 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087701 : List Nat := [1, 3, 2, 1, 4, 2, 1, 2, 3, 2, 2]
def baseStart_6087701 : Nat := 118140960795 + 6087701 * 2 ^ 59
def prefixEnd_6087701 : Nat := 4983230072969 + 3 ^ 40 * 6087701 * 2
def baseEnd_6087701 : Nat := 3125916693856591575540679

theorem tailTrace_6087701 : CollatzResearch.WordTrace tailWord_6087701 prefixEnd_6087701 3125916693856591575540679 := by
  unfold tailWord_6087701
  simp only [CollatzResearch.WordTrace]
  refine ⟨222036696518306448401438957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148024464345537632267625971 222036696518306448401438957)
  ·
    refine ⟨83263761194364918150539609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222036696518306448401438957 83263761194364918150539609)
    ·
      refine ⟨62447820895773688612904707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83263761194364918150539609 62447820895773688612904707)
      ·
        refine ⟨93671731343660532919357061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62447820895773688612904707 93671731343660532919357061)
        ·
          refine ⟨17563449626936349922379449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93671731343660532919357061 17563449626936349922379449)
          ·
            refine ⟨13172587220202262441784587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17563449626936349922379449 13172587220202262441784587)
            ·
              refine ⟨19758880830303393662676881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13172587220202262441784587 19758880830303393662676881)
              ·
                refine ⟨14819160622727545247007661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19758880830303393662676881 14819160622727545247007661)
                ·
                  refine ⟨5557185233522829467627873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14819160622727545247007661 5557185233522829467627873)
                  ·
                    refine ⟨4167888925142122100720905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5557185233522829467627873 4167888925142122100720905)
                    ·
                      refine ⟨3125916693856591575540679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4167888925142122100720905 3125916693856591575540679)
                      ·
                        rfl

theorem cell23_6087701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 2, 3, 2, 2].length) (baseStart_6087701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087701 prefixEnd_6087701 := by exact prefixLift 6087701
  have htrace : WordTrace (prefixWord ++ tailWord_6087701) baseStart_6087701 baseEnd_6087701 := by
    simpa [prefixWord, tailWord_6087701, baseEnd_6087701] using wordTrace_append hprefix tailTrace_6087701
  have hstable : (prefixWord ++ tailWord_6087701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087701).length < 2 ^ (prefixWord ++ tailWord_6087701).sum := by decide
  have hdescent : baseEnd_6087701 < baseStart_6087701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087717 : List Nat := [1, 3, 1, 2, 2, 2, 1, 4, 1, 3, 3]
def baseStart_6087717 : Nat := 118140960795 + 6087717 * 2 ^ 59
def prefixEnd_6087717 : Nat := 4983230072969 + 3 ^ 40 * 6087717 * 2
def baseEnd_6087717 : Nat := 3125924909547063512940605

theorem tailTrace_6087717 : CollatzResearch.WordTrace tailWord_6087717 prefixEnd_6087717 3125924909547063512940605 := by
  unfold tailWord_6087717
  simp only [CollatzResearch.WordTrace]
  refine ⟨222037280086248483134021405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148024853390832322089347603 222037280086248483134021405)
  ·
    refine ⟨83263980032343181175258027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222037280086248483134021405 83263980032343181175258027)
    ·
      refine ⟨124895970048514771762887041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83263980032343181175258027 124895970048514771762887041)
      ·
        refine ⟨93671977536386078822165281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124895970048514771762887041 93671977536386078822165281)
        ·
          refine ⟨70253983152289559116623961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93671977536386078822165281 70253983152289559116623961)
          ·
            refine ⟨52690487364217169337467971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70253983152289559116623961 52690487364217169337467971)
            ·
              refine ⟨79035731046325754006201957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52690487364217169337467971 79035731046325754006201957)
              ·
                refine ⟨14819199571186078876162867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79035731046325754006201957 14819199571186078876162867)
                ·
                  refine ⟨22228799356779118314244301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14819199571186078876162867 22228799356779118314244301)
                  ·
                    refine ⟨8335799758792169367841613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22228799356779118314244301 8335799758792169367841613)
                    ·
                      refine ⟨3125924909547063512940605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8335799758792169367841613 3125924909547063512940605)
                      ·
                        rfl

theorem cell23_6087717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 4, 1, 3, 3].length) (baseStart_6087717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087717 prefixEnd_6087717 := by exact prefixLift 6087717
  have htrace : WordTrace (prefixWord ++ tailWord_6087717) baseStart_6087717 baseEnd_6087717 := by
    simpa [prefixWord, tailWord_6087717, baseEnd_6087717] using wordTrace_append hprefix tailTrace_6087717
  have hstable : (prefixWord ++ tailWord_6087717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087717).length < 2 ^ (prefixWord ++ tailWord_6087717).sum := by decide
  have hdescent : baseEnd_6087717 < baseStart_6087717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087760 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 5]
def baseStart_6087760 : Nat := 118140960795 + 6087760 * 2 ^ 59
def prefixEnd_6087760 : Nat := 4983230072969 + 3 ^ 40 * 6087760 * 2
def baseEnd_6087760 : Nat := 3125946989215206844702907

theorem tailTrace_6087760 : CollatzResearch.WordTrace tailWord_6087760 prefixEnd_6087760 3125946989215206844702907 := by
  unfold tailWord_6087760
  simp only [CollatzResearch.WordTrace]
  refine ⟨111019424212546350738918367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148025898950061800985224489 111019424212546350738918367)
  ·
    refine ⟨166529136318819526108377551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111019424212546350738918367 166529136318819526108377551)
    ·
      refine ⟨249793704478229289162566327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166529136318819526108377551 249793704478229289162566327)
      ·
        refine ⟨374690556717343933743849491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249793704478229289162566327 374690556717343933743849491)
        ·
          refine ⟨562035835076015900615774237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374690556717343933743849491 562035835076015900615774237)
          ·
            refine ⟨210763438153505962730915339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 562035835076015900615774237 210763438153505962730915339)
            ·
              refine ⟨316145157230258944096373009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210763438153505962730915339 316145157230258944096373009)
              ·
                refine ⟨237108867922694208072279757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 316145157230258944096373009 237108867922694208072279757)
                ·
                  refine ⟨88915825471010328027104909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 237108867922694208072279757 88915825471010328027104909)
                  ·
                    refine ⟨33343434551628873010164341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88915825471010328027104909 33343434551628873010164341)
                    ·
                      refine ⟨3125946989215206844702907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33343434551628873010164341 3125946989215206844702907)
                      ·
                        rfl

theorem cell23_6087760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 5].length) (baseStart_6087760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087760 prefixEnd_6087760 := by exact prefixLift 6087760
  have htrace : WordTrace (prefixWord ++ tailWord_6087760) baseStart_6087760 baseEnd_6087760 := by
    simpa [prefixWord, tailWord_6087760, baseEnd_6087760] using wordTrace_append hprefix tailTrace_6087760
  have hstable : (prefixWord ++ tailWord_6087760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087760).length < 2 ^ (prefixWord ++ tailWord_6087760).sum := by decide
  have hdescent : baseEnd_6087760 < baseStart_6087760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087778 : List Nat := [3, 3, 2, 2, 1, 1, 2, 3, 1, 3, 2]
def baseStart_6087778 : Nat := 118140960795 + 6087778 * 2 ^ 59
def prefixEnd_6087778 : Nat := 4983230072969 + 3 ^ 40 * 6087778 * 2
def baseEnd_6087778 : Nat := 3125956231866987774277825

theorem tailTrace_6087778 : CollatzResearch.WordTrace tailWord_6087778 prefixEnd_6087778 3125956231866987774277825 := by
  unfold tailWord_6087778
  simp only [CollatzResearch.WordTrace]
  refine ⟨55509876234756872637997997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148026336626018327034661325 55509876234756872637997997)
  ·
    refine ⟨20816203588033827239249249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55509876234756872637997997 20816203588033827239249249)
    ·
      refine ⟨15612152691025370429436937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20816203588033827239249249 15612152691025370429436937)
      ·
        refine ⟨11709114518269027822077703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15612152691025370429436937 11709114518269027822077703)
        ·
          refine ⟨17563671777403541733116555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11709114518269027822077703 17563671777403541733116555)
          ·
            refine ⟨26345507666105312599674833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17563671777403541733116555 26345507666105312599674833)
            ·
              refine ⟨19759130749578984449756125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26345507666105312599674833 19759130749578984449756125)
              ·
                refine ⟨7409674031092119168658547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19759130749578984449756125 7409674031092119168658547)
                ·
                  refine ⟨11114511046638178752987821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7409674031092119168658547 11114511046638178752987821)
                  ·
                    refine ⟨4167941642489317032370433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11114511046638178752987821 4167941642489317032370433)
                    ·
                      refine ⟨3125956231866987774277825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4167941642489317032370433 3125956231866987774277825)
                      ·
                        rfl

theorem cell23_6087778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_6087778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087778 prefixEnd_6087778 := by exact prefixLift 6087778
  have htrace : WordTrace (prefixWord ++ tailWord_6087778) baseStart_6087778 baseEnd_6087778 := by
    simpa [prefixWord, tailWord_6087778, baseEnd_6087778] using wordTrace_append hprefix tailTrace_6087778
  have hstable : (prefixWord ++ tailWord_6087778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087778).length < 2 ^ (prefixWord ++ tailWord_6087778).sum := by decide
  have hdescent : baseEnd_6087778 < baseStart_6087778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087791 : List Nat := [1, 1, 2, 1, 3, 3, 2, 4, 2, 2, 2]
def baseStart_6087791 : Nat := 118140960795 + 6087791 * 2 ^ 59
def prefixEnd_6087791 : Nat := 4983230072969 + 3 ^ 40 * 6087791 * 2
def baseEnd_6087791 : Nat := 3125962907115496223415265

theorem tailTrace_6087791 : CollatzResearch.WordTrace tailWord_6087791 prefixEnd_6087791 3125962907115496223415265 := by
  unfold tailWord_6087791
  simp only [CollatzResearch.WordTrace]
  refine ⟨222039979087980393772215227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148026652725320262514810151 222039979087980393772215227)
  ·
    refine ⟨333059968631970590658322841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222039979087980393772215227 333059968631970590658322841)
    ·
      refine ⟨249794976473977942993742131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333059968631970590658322841 249794976473977942993742131)
      ·
        refine ⟨374692464710966914490613197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249794976473977942993742131 374692464710966914490613197)
        ·
          refine ⟨140509674266612592933979949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 374692464710966914490613197 140509674266612592933979949)
          ·
            refine ⟨52691127849979722350242481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140509674266612592933979949 52691127849979722350242481)
            ·
              refine ⟨39518345887484791762681861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52691127849979722350242481 39518345887484791762681861)
              ·
                refine ⟨7409689853903398455502849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39518345887484791762681861 7409689853903398455502849)
                ·
                  refine ⟨5557267390427548841627137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7409689853903398455502849 5557267390427548841627137)
                  ·
                    refine ⟨4167950542820661631220353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5557267390427548841627137 4167950542820661631220353)
                    ·
                      refine ⟨3125962907115496223415265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4167950542820661631220353 3125962907115496223415265)
                      ·
                        rfl

theorem cell23_6087791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 4, 2, 2, 2].length) (baseStart_6087791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087791 prefixEnd_6087791 := by exact prefixLift 6087791
  have htrace : WordTrace (prefixWord ++ tailWord_6087791) baseStart_6087791 baseEnd_6087791 := by
    simpa [prefixWord, tailWord_6087791, baseEnd_6087791] using wordTrace_append hprefix tailTrace_6087791
  have hstable : (prefixWord ++ tailWord_6087791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087791).length < 2 ^ (prefixWord ++ tailWord_6087791).sum := by decide
  have hdescent : baseEnd_6087791 < baseStart_6087791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087808 : List Nat := [2, 1, 1, 2, 1, 3, 6, 1, 2, 2, 2]
def baseStart_6087808 : Nat := 118140960795 + 6087808 * 2 ^ 59
def prefixEnd_6087808 : Nat := 4983230072969 + 3 ^ 40 * 6087808 * 2
def baseEnd_6087808 : Nat := 3125971636286622656902687

theorem tailTrace_6087808 : CollatzResearch.WordTrace tailWord_6087808 prefixEnd_6087808 3125971636286622656902687 := by
  unfold tailWord_6087808
  simp only [CollatzResearch.WordTrace]
  refine ⟨111020299564459402837792039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148027066085945870450389385 111020299564459402837792039)
  ·
    refine ⟨166530449346689104256688059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111020299564459402837792039 166530449346689104256688059)
    ·
      refine ⟨249795674020033656385032089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166530449346689104256688059 249795674020033656385032089)
      ·
        refine ⟨187346755515025242288774067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249795674020033656385032089 187346755515025242288774067)
        ·
          refine ⟨281020133272537863433161101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187346755515025242288774067 281020133272537863433161101)
          ·
            refine ⟨105382549977201698787435413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 281020133272537863433161101 105382549977201698787435413)
            ·
              refine ⟨4939807030181329630661035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 105382549977201698787435413 4939807030181329630661035)
              ·
                refine ⟨7409710545271994445991553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4939807030181329630661035 7409710545271994445991553)
                ·
                  refine ⟨5557282908953995834493665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7409710545271994445991553 5557282908953995834493665)
                  ·
                    refine ⟨4167962181715496875870249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5557282908953995834493665 4167962181715496875870249)
                    ·
                      refine ⟨3125971636286622656902687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4167962181715496875870249 3125971636286622656902687)
                      ·
                        rfl

theorem cell23_6087808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 2, 2, 2].length) (baseStart_6087808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087808 prefixEnd_6087808 := by exact prefixLift 6087808
  have htrace : WordTrace (prefixWord ++ tailWord_6087808) baseStart_6087808 baseEnd_6087808 := by
    simpa [prefixWord, tailWord_6087808, baseEnd_6087808] using wordTrace_append hprefix tailTrace_6087808
  have hstable : (prefixWord ++ tailWord_6087808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087808).length < 2 ^ (prefixWord ++ tailWord_6087808).sum := by decide
  have hdescent : baseEnd_6087808 < baseStart_6087808 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087827 : List Nat := [1, 1, 1, 2, 1, 2, 5, 3, 2, 5]
def baseStart_6087827 : Nat := 118140960795 + 6087827 * 2 ^ 59
def prefixEnd_6087827 : Nat := 4983230072969 + 3 ^ 40 * 6087827 * 2
def baseEnd_6087827 : Nat := 1041993797473019360855033

theorem tailTrace_6087827 : CollatzResearch.WordTrace tailWord_6087827 prefixEnd_6087827 1041993797473019360855033 := by
  unfold tailWord_6087827
  simp only [CollatzResearch.WordTrace]
  refine ⟨222041292115849971920525735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148027528077233314613683823 222041292115849971920525735)
  ·
    refine ⟨333061938173774957880788603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222041292115849971920525735 333061938173774957880788603)
    ·
      refine ⟨499592907260662436821182905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333061938173774957880788603 499592907260662436821182905)
      ·
        refine ⟨374694680445496827615887179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 499592907260662436821182905 374694680445496827615887179)
        ·
          refine ⟨562042020668245241423830769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374694680445496827615887179 562042020668245241423830769)
          ·
            refine ⟨421531515501183931067873077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 562042020668245241423830769 421531515501183931067873077)
            ·
              refine ⟨39518579578235993537613101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 421531515501183931067873077 39518579578235993537613101)
              ·
                refine ⟨14819467341838497576604913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39518579578235993537613101 14819467341838497576604913)
                ·
                  refine ⟨11114600506378873182453685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14819467341838497576604913 11114600506378873182453685)
                  ·
                    refine ⟨1041993797473019360855033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11114600506378873182453685 1041993797473019360855033)
                    ·
                      rfl

theorem cell23_6087827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 2, 5].length) (baseStart_6087827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087827 prefixEnd_6087827 := by exact prefixLift 6087827
  have htrace : WordTrace (prefixWord ++ tailWord_6087827) baseStart_6087827 baseEnd_6087827 := by
    simpa [prefixWord, tailWord_6087827, baseEnd_6087827] using wordTrace_append hprefix tailTrace_6087827
  have hstable : (prefixWord ++ tailWord_6087827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087827).length < 2 ^ (prefixWord ++ tailWord_6087827).sum := by decide
  have hdescent : baseEnd_6087827 < baseStart_6087827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087837 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 3, 2, 5]
def baseStart_6087837 : Nat := 118140960795 + 6087837 * 2 ^ 59
def prefixEnd_6087837 : Nat := 4983230072969 + 3 ^ 40 * 6087837 * 2
def baseEnd_6087837 : Nat := 3125986527225603043440053

theorem tailTrace_6087837 : CollatzResearch.WordTrace tailWord_6087837 prefixEnd_6087837 3125986527225603043440053 := by
  unfold tailWord_6087837
  simp only [CollatzResearch.WordTrace]
  refine ⟨222041656845813743628389765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148027771230542495752259843 222041656845813743628389765)
  ·
    refine ⟨41632810658590076930323081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222041656845813743628389765 41632810658590076930323081)
    ·
      refine ⟨31224607993942557697742311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41632810658590076930323081 31224607993942557697742311)
      ·
        refine ⟨46836911990913836546613467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31224607993942557697742311 46836911990913836546613467)
        ·
          refine ⟨70255367986370754819920201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46836911990913836546613467 70255367986370754819920201)
          ·
            refine ⟨52691525989778066114940151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70255367986370754819920201 52691525989778066114940151)
            ·
              refine ⟨79037288984667099172410227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52691525989778066114940151 79037288984667099172410227)
              ·
                refine ⟨118555933477000648758615341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79037288984667099172410227 118555933477000648758615341)
                ·
                  refine ⟨44458475053875243284480753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118555933477000648758615341 44458475053875243284480753)
                  ·
                    refine ⟨33343856290406432463360565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44458475053875243284480753 33343856290406432463360565)
                    ·
                      refine ⟨3125986527225603043440053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33343856290406432463360565 3125986527225603043440053)
                      ·
                        rfl

theorem cell23_6087837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_6087837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087837 prefixEnd_6087837 := by exact prefixLift 6087837
  have htrace : WordTrace (prefixWord ++ tailWord_6087837) baseStart_6087837 baseEnd_6087837 := by
    simpa [prefixWord, tailWord_6087837, baseEnd_6087837] using wordTrace_append hprefix tailTrace_6087837
  have hstable : (prefixWord ++ tailWord_6087837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087837).length < 2 ^ (prefixWord ++ tailWord_6087837).sum := by decide
  have hdescent : baseEnd_6087837 < baseStart_6087837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087844 : List Nat := [2, 3, 1, 2, 3, 1, 2, 2, 2, 5]
def baseStart_6087844 : Nat := 118140960795 + 6087844 * 2 ^ 59
def prefixEnd_6087844 : Nat := 4983230072969 + 3 ^ 40 * 6087844 * 2
def baseEnd_6087844 : Nat := 1041996707196728172017507

theorem tailTrace_6087844 : CollatzResearch.WordTrace tailWord_6087844 prefixEnd_6087844 1041996707196728172017507 := by
  unfold tailWord_6087844
  simp only [CollatzResearch.WordTrace]
  refine ⟨111020956078394191911947293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148027941437858922549263057 111020956078394191911947293)
  ·
    refine ⟨41632858529397821966980235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111020956078394191911947293 41632858529397821966980235)
    ·
      refine ⟨62449287794096732950470353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41632858529397821966980235 62449287794096732950470353)
      ·
        refine ⟨46836965845572549712852765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62449287794096732950470353 46836965845572549712852765)
        ·
          refine ⟨17563862192089706142319787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46836965845572549712852765 17563862192089706142319787)
          ·
            refine ⟨26345793288134559213479681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17563862192089706142319787 26345793288134559213479681)
            ·
              refine ⟨19759344966100919410109761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26345793288134559213479681 19759344966100919410109761)
              ·
                refine ⟨14819508724575689557582321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19759344966100919410109761 14819508724575689557582321)
                ·
                  refine ⟨11114631543431767168186741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14819508724575689557582321 11114631543431767168186741)
                  ·
                    refine ⟨1041996707196728172017507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11114631543431767168186741 1041996707196728172017507)
                    ·
                      rfl

theorem cell23_6087844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_6087844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087844 prefixEnd_6087844 := by exact prefixLift 6087844
  have htrace : WordTrace (prefixWord ++ tailWord_6087844) baseStart_6087844 baseEnd_6087844 := by
    simpa [prefixWord, tailWord_6087844, baseEnd_6087844] using wordTrace_append hprefix tailTrace_6087844
  have hstable : (prefixWord ++ tailWord_6087844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087844).length < 2 ^ (prefixWord ++ tailWord_6087844).sum := by decide
  have hdescent : baseEnd_6087844 < baseStart_6087844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087904 : List Nat := [2, 1, 1, 3, 1, 4, 3, 2, 6]
def baseStart_6087904 : Nat := 118140960795 + 6087904 * 2 ^ 59
def prefixEnd_6087904 : Nat := 4983230072969 + 3 ^ 40 * 6087904 * 2
def baseEnd_6087904 : Nat := 347335658936606031255805

theorem tailTrace_6087904 : CollatzResearch.WordTrace tailWord_6087904 prefixEnd_6087904 347335658936606031255805 := by
  unfold tailWord_6087904
  simp only [CollatzResearch.WordTrace]
  refine ⟨111022050268285507035539383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148029400357714009380719177 111022050268285507035539383)
  ·
    refine ⟨166533075402428260553309075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111022050268285507035539383 166533075402428260553309075)
    ·
      refine ⟨249799613103642390829963613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166533075402428260553309075 249799613103642390829963613)
      ·
        refine ⟨93674854913865896561236355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249799613103642390829963613 93674854913865896561236355)
        ·
          refine ⟨140512282370798844841854533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93674854913865896561236355 140512282370798844841854533)
          ·
            refine ⟨26346052944524783407847725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140512282370798844841854533 26346052944524783407847725)
            ·
              refine ⟨9879769854196793777942897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26346052944524783407847725 9879769854196793777942897)
              ·
                refine ⟨7409827390647595333457173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9879769854196793777942897 7409827390647595333457173)
                ·
                  refine ⟨347335658936606031255805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7409827390647595333457173 347335658936606031255805)
                  ·
                    rfl

theorem cell23_6087904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 6].length) (baseStart_6087904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087904 prefixEnd_6087904 := by exact prefixLift 6087904
  have htrace : WordTrace (prefixWord ++ tailWord_6087904) baseStart_6087904 baseEnd_6087904 := by
    simpa [prefixWord, tailWord_6087904, baseEnd_6087904] using wordTrace_append hprefix tailTrace_6087904
  have hstable : (prefixWord ++ tailWord_6087904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087904).length < 2 ^ (prefixWord ++ tailWord_6087904).sum := by decide
  have hdescent : baseEnd_6087904 < baseStart_6087904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087941 : List Nat := [1, 3, 1, 1, 2, 1, 4, 3, 2, 3, 2]
def baseStart_6087941 : Nat := 118140960795 + 6087941 * 2 ^ 59
def prefixEnd_6087941 : Nat := 4983230072969 + 3 ^ 40 * 6087941 * 2
def baseEnd_6087941 : Nat := 3126039929213670636539575

theorem tailTrace_6087941 : CollatzResearch.WordTrace tailWord_6087941 prefixEnd_6087941 3126039929213670636539575 := by
  unfold tailWord_6087941
  simp only [CollatzResearch.WordTrace]
  refine ⟨222045450037436969390175677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148030300024957979593450451 222045450037436969390175677)
  ·
    refine ⟨83267043764038863521315879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222045450037436969390175677 83267043764038863521315879)
    ·
      refine ⟨124900565646058295281973819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83267043764038863521315879 124900565646058295281973819)
      ·
        refine ⟨187350848469087442922960729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124900565646058295281973819 187350848469087442922960729)
        ·
          refine ⟨140513136351815582192220547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187350848469087442922960729 140513136351815582192220547)
          ·
            refine ⟨210769704527723373288330821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140513136351815582192220547 210769704527723373288330821)
            ·
              refine ⟨39519319598948132491562029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 210769704527723373288330821 39519319598948132491562029)
              ·
                refine ⟨14819744849605549684335761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39519319598948132491562029 14819744849605549684335761)
                ·
                  refine ⟨11114808637204162263251821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14819744849605549684335761 11114808637204162263251821)
                  ·
                    refine ⟨4168053238951560848719433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11114808637204162263251821 4168053238951560848719433)
                    ·
                      refine ⟨3126039929213670636539575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4168053238951560848719433 3126039929213670636539575)
                      ·
                        rfl

theorem cell23_6087941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 3, 2].length) (baseStart_6087941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087941 prefixEnd_6087941 := by exact prefixLift 6087941
  have htrace : WordTrace (prefixWord ++ tailWord_6087941) baseStart_6087941 baseEnd_6087941 := by
    simpa [prefixWord, tailWord_6087941, baseEnd_6087941] using wordTrace_append hprefix tailTrace_6087941
  have hstable : (prefixWord ++ tailWord_6087941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087941).length < 2 ^ (prefixWord ++ tailWord_6087941).sum := by decide
  have hdescent : baseEnd_6087941 < baseStart_6087941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087965 : List Nat := [1, 4, 2, 3, 1, 3, 1, 1, 3, 1, 3]
def baseStart_6087965 : Nat := 118140960795 + 6087965 * 2 ^ 59
def prefixEnd_6087965 : Nat := 4983230072969 + 3 ^ 40 * 6087965 * 2
def baseEnd_6087965 : Nat := 3126052252749378542639465

theorem tailTrace_6087965 : CollatzResearch.WordTrace tailWord_6087965 prefixEnd_6087965 3126052252749378542639465 := by
  unfold tailWord_6087965
  simp only [CollatzResearch.WordTrace]
  refine ⟨222046325389350021489049349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148030883592900014326032899 222046325389350021489049349)
  ·
    refine ⟨41633686010503129029196753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222046325389350021489049349 41633686010503129029196753)
    ·
      refine ⟨31225264507877346771897565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41633686010503129029196753 31225264507877346771897565)
      ·
        refine ⟨11709474190454005039461587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31225264507877346771897565 11709474190454005039461587)
        ·
          refine ⟨17564211285681007559192381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11709474190454005039461587 17564211285681007559192381)
          ·
            refine ⟨6586579232130377834697143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17564211285681007559192381 6586579232130377834697143)
            ·
              refine ⟨9879868848195566752045715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6586579232130377834697143 9879868848195566752045715)
              ·
                refine ⟨14819803272293350128068573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9879868848195566752045715 14819803272293350128068573)
                ·
                  refine ⟨5557426227110006298025715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14819803272293350128068573 5557426227110006298025715)
                  ·
                    refine ⟨8336139340665009447038573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5557426227110006298025715 8336139340665009447038573)
                    ·
                      refine ⟨3126052252749378542639465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8336139340665009447038573 3126052252749378542639465)
                      ·
                        rfl

theorem cell23_6087965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_6087965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087965 prefixEnd_6087965 := by exact prefixLift 6087965
  have htrace : WordTrace (prefixWord ++ tailWord_6087965) baseStart_6087965 baseEnd_6087965 := by
    simpa [prefixWord, tailWord_6087965, baseEnd_6087965] using wordTrace_append hprefix tailTrace_6087965
  have hstable : (prefixWord ++ tailWord_6087965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087965).length < 2 ^ (prefixWord ++ tailWord_6087965).sum := by decide
  have hdescent : baseEnd_6087965 < baseStart_6087965 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6087984 : List Nat := [2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 4]
def baseStart_6087984 : Nat := 118140960795 + 6087984 * 2 ^ 59
def prefixEnd_6087984 : Nat := 4983230072969 + 3 ^ 40 * 6087984 * 2
def baseEnd_6087984 : Nat := 3126062008881813968301877

theorem tailTrace_6087984 : CollatzResearch.WordTrace tailWord_6087984 prefixEnd_6087984 3126062008881813968301877 := by
  unfold tailWord_6087984
  simp only [CollatzResearch.WordTrace]
  refine ⟨111023509188140593866995503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148031345584187458489327337 111023509188140593866995503)
  ·
    refine ⟨166535263782210890800493255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111023509188140593866995503 166535263782210890800493255)
    ·
      refine ⟨249802895673316336200739883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166535263782210890800493255 249802895673316336200739883)
      ·
        refine ⟨374704343509974504301109825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249802895673316336200739883 374704343509974504301109825)
        ·
          refine ⟨281028257632480878225832369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374704343509974504301109825 281028257632480878225832369)
          ·
            refine ⟨210771193224360658669374277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281028257632480878225832369 210771193224360658669374277)
            ·
              refine ⟨39519598729567623500507677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 210771193224360658669374277 39519598729567623500507677)
              ·
                refine ⟨14819849523587858812690379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39519598729567623500507677 14819849523587858812690379)
                ·
                  refine ⟨22229774285381788219035569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14819849523587858812690379 22229774285381788219035569)
                  ·
                    refine ⟨16672330714036341164276677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22229774285381788219035569 16672330714036341164276677)
                    ·
                      refine ⟨3126062008881813968301877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16672330714036341164276677 3126062008881813968301877)
                      ·
                        rfl

theorem cell23_6087984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 4].length) (baseStart_6087984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6087984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6087984 prefixEnd_6087984 := by exact prefixLift 6087984
  have htrace : WordTrace (prefixWord ++ tailWord_6087984) baseStart_6087984 baseEnd_6087984 := by
    simpa [prefixWord, tailWord_6087984, baseEnd_6087984] using wordTrace_append hprefix tailTrace_6087984
  have hstable : (prefixWord ++ tailWord_6087984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6087984).length < 2 ^ (prefixWord ++ tailWord_6087984).sum := by decide
  have hdescent : baseEnd_6087984 < baseStart_6087984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6087984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088001 : List Nat := [1, 2, 5, 2, 1, 1, 1, 1, 3, 2, 4]
def baseStart_6088001 : Nat := 118140960795 + 6088001 * 2 ^ 59
def prefixEnd_6088001 : Nat := 4983230072969 + 3 ^ 40 * 6088001 * 2
def baseEnd_6088001 : Nat := 3126070738052940401789299

theorem tailTrace_6088001 : CollatzResearch.WordTrace tailWord_6088001 prefixEnd_6088001 3126070738052940401789299 := by
  unfold tailWord_6088001
  simp only [CollatzResearch.WordTrace]
  refine ⟨222047638417219599637359857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148031758944813066424906571 222047638417219599637359857)
  ·
    refine ⟨166535728812914699728019893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222047638417219599637359857 166535728812914699728019893)
    ·
      refine ⟨15612724576210753099501865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 166535728812914699728019893 15612724576210753099501865)
      ·
        refine ⟨11709543432158064824626399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15612724576210753099501865 11709543432158064824626399)
        ·
          refine ⟨17564315148237097236939599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11709543432158064824626399 17564315148237097236939599)
          ·
            refine ⟨26346472722355645855409399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17564315148237097236939599 26346472722355645855409399)
            ·
              refine ⟨39519709083533468783114099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26346472722355645855409399 39519709083533468783114099)
              ·
                refine ⟨59279563625300203174671149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39519709083533468783114099 59279563625300203174671149)
                ·
                  refine ⟨22229836359487576190501681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59279563625300203174671149 22229836359487576190501681)
                  ·
                    refine ⟨16672377269615682142876261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22229836359487576190501681 16672377269615682142876261)
                    ·
                      refine ⟨3126070738052940401789299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16672377269615682142876261 3126070738052940401789299)
                      ·
                        rfl

theorem cell23_6088001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_6088001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088001 prefixEnd_6088001 := by exact prefixLift 6088001
  have htrace : WordTrace (prefixWord ++ tailWord_6088001) baseStart_6088001 baseEnd_6088001 := by
    simpa [prefixWord, tailWord_6088001, baseEnd_6088001] using wordTrace_append hprefix tailTrace_6088001
  have hstable : (prefixWord ++ tailWord_6088001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088001).length < 2 ^ (prefixWord ++ tailWord_6088001).sum := by decide
  have hdescent : baseEnd_6088001 < baseStart_6088001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088048 : List Nat := [2, 1, 1, 1, 4, 2, 2, 4, 1, 3, 2]
def baseStart_6088048 : Nat := 118140960795 + 6088048 * 2 ^ 59
def prefixEnd_6088048 : Nat := 4983230072969 + 3 ^ 40 * 6088048 * 2
def baseEnd_6088048 : Nat := 3126094871643701717901583

theorem tailTrace_6088048 : CollatzResearch.WordTrace tailWord_6088048 prefixEnd_6088048 3126094871643701717901583 := by
  unfold tailWord_6088048
  simp only [CollatzResearch.WordTrace]
  refine ⟨111024676324024663332160399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148032901765366217776213865 111024676324024663332160399)
  ·
    refine ⟨166537014486036994998240599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111024676324024663332160399 166537014486036994998240599)
    ·
      refine ⟨249805521729055492497360899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166537014486036994998240599 249805521729055492497360899)
      ·
        refine ⟨374708282593583238746041349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249805521729055492497360899 374708282593583238746041349)
        ·
          refine ⟨70257802986296857264882753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 374708282593583238746041349 70257802986296857264882753)
          ·
            refine ⟨52693352239722642948662065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70257802986296857264882753 52693352239722642948662065)
            ·
              refine ⟨39520014179791982211496549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52693352239722642948662065 39520014179791982211496549)
              ·
                refine ⟨7410002658710996664655603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39520014179791982211496549 7410002658710996664655603)
                ·
                  refine ⟨11115003988066494996983405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7410002658710996664655603 11115003988066494996983405)
                  ·
                    refine ⟨4168126495524935623868777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11115003988066494996983405 4168126495524935623868777)
                    ·
                      refine ⟨3126094871643701717901583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4168126495524935623868777 3126094871643701717901583)
                      ·
                        rfl

theorem cell23_6088048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 1, 3, 2].length) (baseStart_6088048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088048 prefixEnd_6088048 := by exact prefixLift 6088048
  have htrace : WordTrace (prefixWord ++ tailWord_6088048) baseStart_6088048 baseEnd_6088048 := by
    simpa [prefixWord, tailWord_6088048, baseEnd_6088048] using wordTrace_append hprefix tailTrace_6088048
  have hstable : (prefixWord ++ tailWord_6088048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088048).length < 2 ^ (prefixWord ++ tailWord_6088048).sum := by decide
  have hdescent : baseEnd_6088048 < baseStart_6088048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088064 : List Nat := [2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 5]
def baseStart_6088064 : Nat := 118140960795 + 6088064 * 2 ^ 59
def prefixEnd_6088064 : Nat := 4983230072969 + 3 ^ 40 * 6088064 * 2
def baseEnd_6088064 : Nat := 3126103087334173655301509

theorem tailTrace_6088064 : CollatzResearch.WordTrace tailWord_6088064 prefixEnd_6088064 3126103087334173655301509 := by
  unfold tailWord_6088064
  simp only [CollatzResearch.WordTrace]
  refine ⟨111024968107995680698451623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148033290810660907597935497 111024968107995680698451623)
  ·
    refine ⟨166537452161993521047677435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111024968107995680698451623 166537452161993521047677435)
    ·
      refine ⟨249806178242990281571516153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166537452161993521047677435 249806178242990281571516153)
      ·
        refine ⟨187354633682242711178637115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249806178242990281571516153 187354633682242711178637115)
        ·
          refine ⟨281031950523364066767955673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187354633682242711178637115 281031950523364066767955673)
          ·
            refine ⟨210773962892523050075966755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281031950523364066767955673 210773962892523050075966755)
            ·
              refine ⟨316160944338784575113950133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210773962892523050075966755 316160944338784575113950133)
              ·
                refine ⟨29640088531761053916932825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 316160944338784575113950133 29640088531761053916932825)
                ·
                  refine ⟨22230066398820790437699619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29640088531761053916932825 22230066398820790437699619)
                  ·
                    refine ⟨33345099598231185656549429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22230066398820790437699619 33345099598231185656549429)
                    ·
                      refine ⟨3126103087334173655301509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33345099598231185656549429 3126103087334173655301509)
                      ·
                        rfl

theorem cell23_6088064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 5].length) (baseStart_6088064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088064 prefixEnd_6088064 := by exact prefixLift 6088064
  have htrace : WordTrace (prefixWord ++ tailWord_6088064) baseStart_6088064 baseEnd_6088064 := by
    simpa [prefixWord, tailWord_6088064, baseEnd_6088064] using wordTrace_append hprefix tailTrace_6088064
  have hstable : (prefixWord ++ tailWord_6088064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088064).length < 2 ^ (prefixWord ++ tailWord_6088064).sum := by decide
  have hdescent : baseEnd_6088064 < baseStart_6088064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088095 : List Nat := [1, 1, 2, 5, 1, 4, 1, 1, 1, 4, 2]
def baseStart_6088095 : Nat := 118140960795 + 6088095 * 2 ^ 59
def prefixEnd_6088095 : Nat := 4983230072969 + 3 ^ 40 * 6088095 * 2
def baseEnd_6088095 : Nat := 3126119005234463034013867

theorem tailTrace_6088095 : CollatzResearch.WordTrace tailWord_6088095 prefixEnd_6088095 3126119005234463034013867 := by
  unfold tailWord_6088095
  simp only [CollatzResearch.WordTrace]
  refine ⟨222051066878879053691281739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148034044585919369127521159 222051066878879053691281739)
  ·
    refine ⟨333076600318318580536922609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222051066878879053691281739 333076600318318580536922609)
    ·
      refine ⟨249807450238738935402691957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333076600318318580536922609 249807450238738935402691957)
      ·
        refine ⟨23419448459881775194002371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 249807450238738935402691957 23419448459881775194002371)
        ·
          refine ⟨35129172689822662791003557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23419448459881775194002371 35129172689822662791003557)
          ·
            refine ⟨6586719879341749273313167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35129172689822662791003557 6586719879341749273313167)
            ·
              refine ⟨9880079819012623909969751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6586719879341749273313167 9880079819012623909969751)
              ·
                refine ⟨14820119728518935864954627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9880079819012623909969751 14820119728518935864954627)
                ·
                  refine ⟨22230179592778403797431941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14820119728518935864954627 22230179592778403797431941)
                  ·
                    refine ⟨4168158673645950712018489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22230179592778403797431941 4168158673645950712018489)
                    ·
                      refine ⟨3126119005234463034013867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4168158673645950712018489 3126119005234463034013867)
                      ·
                        rfl

theorem cell23_6088095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_6088095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088095 prefixEnd_6088095 := by exact prefixLift 6088095
  have htrace : WordTrace (prefixWord ++ tailWord_6088095) baseStart_6088095 baseEnd_6088095 := by
    simpa [prefixWord, tailWord_6088095, baseEnd_6088095] using wordTrace_append hprefix tailTrace_6088095
  have hstable : (prefixWord ++ tailWord_6088095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088095).length < 2 ^ (prefixWord ++ tailWord_6088095).sum := by decide
  have hdescent : baseEnd_6088095 < baseStart_6088095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088168 : List Nat := [2, 1, 4, 1, 1, 2, 4, 1, 2, 1, 4]
def baseStart_6088168 : Nat := 118140960795 + 6088168 * 2 ^ 59
def prefixEnd_6088168 : Nat := 4983230072969 + 3 ^ 40 * 6088168 * 2
def baseEnd_6088168 : Nat := 3126156489322241248401031

theorem tailTrace_6088168 : CollatzResearch.WordTrace tailWord_6088168 prefixEnd_6088168 3126156489322241248401031 := by
  unfold tailWord_6088168
  simp only [CollatzResearch.WordTrace]
  refine ⟨111026864703807293579344579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148035819605076391439126105 111026864703807293579344579)
  ·
    refine ⟨166540297055710940369016869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111026864703807293579344579 166540297055710940369016869)
    ·
      refine ⟨31226305697945801319190663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166540297055710940369016869 31226305697945801319190663)
      ·
        refine ⟨46839458546918701978785995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31226305697945801319190663 46839458546918701978785995)
        ·
          refine ⟨70259187820378052968178993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46839458546918701978785995 70259187820378052968178993)
          ·
            refine ⟨52694390865283539726134245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70259187820378052968178993 52694390865283539726134245)
            ·
              refine ⟨9880198287240663698650171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52694390865283539726134245 9880198287240663698650171)
              ·
                refine ⟨14820297430860995547975257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9880198287240663698650171 14820297430860995547975257)
                ·
                  refine ⟨11115223073145746660981443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14820297430860995547975257 11115223073145746660981443)
                  ·
                    refine ⟨16672834609718619991472165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11115223073145746660981443 16672834609718619991472165)
                    ·
                      refine ⟨3126156489322241248401031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16672834609718619991472165 3126156489322241248401031)
                      ·
                        rfl

theorem cell23_6088168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_6088168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088168 prefixEnd_6088168 := by exact prefixLift 6088168
  have htrace : WordTrace (prefixWord ++ tailWord_6088168) baseStart_6088168 baseEnd_6088168 := by
    simpa [prefixWord, tailWord_6088168, baseEnd_6088168] using wordTrace_append hprefix tailTrace_6088168
  have hstable : (prefixWord ++ tailWord_6088168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088168).length < 2 ^ (prefixWord ++ tailWord_6088168).sum := by decide
  have hdescent : baseEnd_6088168 < baseStart_6088168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088188 : List Nat := [2, 2, 2, 1, 2, 1, 4, 2, 2, 2, 3]
def baseStart_6088188 : Nat := 118140960795 + 6088188 * 2 ^ 59
def prefixEnd_6088188 : Nat := 4983230072969 + 3 ^ 40 * 6088188 * 2
def baseEnd_6088188 : Nat := 3126166758935331170150939

theorem tailTrace_6088188 : CollatzResearch.WordTrace tailWord_6088188 prefixEnd_6088188 3126166758935331170150939 := by
  unfold tailWord_6088188
  simp only [CollatzResearch.WordTrace]
  refine ⟨111027229433771065287208609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148036305911694753716278145 111027229433771065287208609)
  ·
    refine ⟨83270422075328298965406457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111027229433771065287208609 83270422075328298965406457)
    ·
      refine ⟨62452816556496224224054843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83270422075328298965406457 62452816556496224224054843)
      ·
        refine ⟨93679224834744336336082265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62452816556496224224054843 93679224834744336336082265)
        ·
          refine ⟨70259418626058252252061699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93679224834744336336082265 70259418626058252252061699)
          ·
            refine ⟨105389127939087378378092549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70259418626058252252061699 105389127939087378378092549)
            ·
              refine ⟨19760461488578883445892353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105389127939087378378092549 19760461488578883445892353)
              ·
                refine ⟨14820346116434162584419265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19760461488578883445892353 14820346116434162584419265)
                ·
                  refine ⟨11115259587325621938314449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14820346116434162584419265 11115259587325621938314449)
                  ·
                    refine ⟨8336444690494216453735837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11115259587325621938314449 8336444690494216453735837)
                    ·
                      refine ⟨3126166758935331170150939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8336444690494216453735837 3126166758935331170150939)
                      ·
                        rfl

theorem cell23_6088188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 2, 2, 3].length) (baseStart_6088188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088188 prefixEnd_6088188 := by exact prefixLift 6088188
  have htrace : WordTrace (prefixWord ++ tailWord_6088188) baseStart_6088188 baseEnd_6088188 := by
    simpa [prefixWord, tailWord_6088188, baseEnd_6088188] using wordTrace_append hprefix tailTrace_6088188
  have hstable : (prefixWord ++ tailWord_6088188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088188).length < 2 ^ (prefixWord ++ tailWord_6088188).sum := by decide
  have hdescent : baseEnd_6088188 < baseStart_6088188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088212 : List Nat := [2, 4, 3, 1, 2, 1, 1, 2, 3, 4]
def baseStart_6088212 : Nat := 118140960795 + 6088212 * 2 ^ 59
def prefixEnd_6088212 : Nat := 4983230072969 + 3 ^ 40 * 6088212 * 2
def baseEnd_6088212 : Nat := 1042059694157013025416943

theorem tailTrace_6088212 : CollatzResearch.WordTrace tailWord_6088212 prefixEnd_6088212 1042059694157013025416943 := by
  unfold tailWord_6088212
  simp only [CollatzResearch.WordTrace]
  refine ⟨111027667109727591336645445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148036889479636788448860593 111027667109727591336645445)
  ·
    refine ⟨20817687583073923375621021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111027667109727591336645445 20817687583073923375621021)
    ·
      refine ⟨7806632843652721265857883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20817687583073923375621021 7806632843652721265857883)
      ·
        refine ⟨11709949265479081898786825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7806632843652721265857883 11709949265479081898786825)
        ·
          refine ⟨8782461949109311424090119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11709949265479081898786825 8782461949109311424090119)
          ·
            refine ⟨13173692923663967136135179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8782461949109311424090119 13173692923663967136135179)
            ·
              refine ⟨19760539385495950704202769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13173692923663967136135179 19760539385495950704202769)
              ·
                refine ⟨14820404539121963028152077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19760539385495950704202769 14820404539121963028152077)
                ·
                  refine ⟨5557651702170736135557029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14820404539121963028152077 5557651702170736135557029)
                  ·
                    refine ⟨1042059694157013025416943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5557651702170736135557029 1042059694157013025416943)
                    ·
                      rfl

theorem cell23_6088212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_6088212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088212 prefixEnd_6088212 := by exact prefixLift 6088212
  have htrace : WordTrace (prefixWord ++ tailWord_6088212) baseStart_6088212 baseEnd_6088212 := by
    simpa [prefixWord, tailWord_6088212, baseEnd_6088212] using wordTrace_append hprefix tailTrace_6088212
  have hstable : (prefixWord ++ tailWord_6088212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088212).length < 2 ^ (prefixWord ++ tailWord_6088212).sum := by decide
  have hdescent : baseEnd_6088212 < baseStart_6088212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088252 : List Nat := [2, 2, 2, 2, 4, 1, 2, 1, 3, 1, 3]
def baseStart_6088252 : Nat := 118140960795 + 6088252 * 2 ^ 59
def prefixEnd_6088252 : Nat := 4983230072969 + 3 ^ 40 * 6088252 * 2
def baseEnd_6088252 : Nat := 3126199621697218919750645

theorem tailTrace_6088252 : CollatzResearch.WordTrace tailWord_6088252 prefixEnd_6088252 3126199621697218919750645 := by
  unfold tailWord_6088252
  simp only [CollatzResearch.WordTrace]
  refine ⟨111028396569655134752373505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148037862092873513003164673 111028396569655134752373505)
  ·
    refine ⟨83271297427241351064280129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111028396569655134752373505 83271297427241351064280129)
    ·
      refine ⟨62453473070431013298210097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83271297427241351064280129 62453473070431013298210097)
      ·
        refine ⟨46840104802823259973657573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62453473070431013298210097 46840104802823259973657573)
        ·
          refine ⟨8782519650529361245060795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46840104802823259973657573 8782519650529361245060795)
          ·
            refine ⟨13173779475794041867591193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8782519650529361245060795 13173779475794041867591193)
            ·
              refine ⟨9880334606845531400693395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13173779475794041867591193 9880334606845531400693395)
              ·
                refine ⟨14820501910268297101040093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9880334606845531400693395 14820501910268297101040093)
                ·
                  refine ⟨5557688216350611412890035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14820501910268297101040093 5557688216350611412890035)
                  ·
                    refine ⟨8336532324525917119335053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5557688216350611412890035 8336532324525917119335053)
                    ·
                      refine ⟨3126199621697218919750645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8336532324525917119335053 3126199621697218919750645)
                      ·
                        rfl

theorem cell23_6088252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_6088252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088252 prefixEnd_6088252 := by exact prefixLift 6088252
  have htrace : WordTrace (prefixWord ++ tailWord_6088252) baseStart_6088252 baseEnd_6088252 := by
    simpa [prefixWord, tailWord_6088252, baseEnd_6088252] using wordTrace_append hprefix tailTrace_6088252
  have hstable : (prefixWord ++ tailWord_6088252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088252).length < 2 ^ (prefixWord ++ tailWord_6088252).sum := by decide
  have hdescent : baseEnd_6088252 < baseStart_6088252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088268 : List Nat := [2, 2, 1, 3, 1, 3, 3, 1, 1, 6]
def baseStart_6088268 : Nat := 118140960795 + 6088268 * 2 ^ 59
def prefixEnd_6088268 : Nat := 4983230072969 + 3 ^ 40 * 6088268 * 2
def baseEnd_6088268 : Nat := 1042069279129230285716857

theorem tailTrace_6088268 : CollatzResearch.WordTrace tailWord_6088268 prefixEnd_6088268 1042069279129230285716857 := by
  unfold tailWord_6088268
  simp only [CollatzResearch.WordTrace]
  refine ⟨111028688353626152118664729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148038251138168202824886305 111028688353626152118664729)
  ·
    refine ⟨83271516265219614088998547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111028688353626152118664729 83271516265219614088998547)
    ·
      refine ⟨124907274397829421133497821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83271516265219614088998547 124907274397829421133497821)
      ·
        refine ⟨46840227899186032925061683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124907274397829421133497821 46840227899186032925061683)
        ·
          refine ⟨70260341848779049387592525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46840227899186032925061683 70260341848779049387592525)
          ·
            refine ⟨26347628193292143520347197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70260341848779049387592525 26347628193292143520347197)
            ·
              refine ⟨9880360572484553820130199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26347628193292143520347197 9880360572484553820130199)
              ·
                refine ⟨14820540858726830730195299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9880360572484553820130199 14820540858726830730195299)
                ·
                  refine ⟨22230811288090246095292949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14820540858726830730195299 22230811288090246095292949)
                  ·
                    refine ⟨1042069279129230285716857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22230811288090246095292949 1042069279129230285716857)
                    ·
                      rfl

theorem cell23_6088268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 1, 6].length) (baseStart_6088268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088268 prefixEnd_6088268 := by exact prefixLift 6088268
  have htrace : WordTrace (prefixWord ++ tailWord_6088268) baseStart_6088268 baseEnd_6088268 := by
    simpa [prefixWord, tailWord_6088268, baseEnd_6088268] using wordTrace_append hprefix tailTrace_6088268
  have hstable : (prefixWord ++ tailWord_6088268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088268).length < 2 ^ (prefixWord ++ tailWord_6088268).sum := by decide
  have hdescent : baseEnd_6088268 < baseStart_6088268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088295 : List Nat := [1, 1, 5, 1, 1, 1, 4, 3, 1, 2, 3]
def baseStart_6088295 : Nat := 118140960795 + 6088295 * 2 ^ 59
def prefixEnd_6088295 : Nat := 4983230072969 + 3 ^ 40 * 6088295 * 2
def baseEnd_6088295 : Nat := 3126221701365362251512947

theorem tailTrace_6088295 : CollatzResearch.WordTrace tailWord_6088295 prefixEnd_6088295 3126221701365362251512947 := by
  unfold tailWord_6088295
  simp only [CollatzResearch.WordTrace]
  refine ⟨222058361478154487848562339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148038907652102991899041559 222058361478154487848562339)
  ·
    refine ⟨333087542217231731772843509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222058361478154487848562339 333087542217231731772843509)
    ·
      refine ⟨31226957082865474853704079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 333087542217231731772843509 31226957082865474853704079)
      ·
        refine ⟨46840435624298212280556119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31226957082865474853704079 46840435624298212280556119)
        ·
          refine ⟨70260653436447318420834179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46840435624298212280556119 70260653436447318420834179)
          ·
            refine ⟨105390980154670977631251269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70260653436447318420834179 105390980154670977631251269)
            ·
              refine ⟨19760808779000808305859613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105390980154670977631251269 19760808779000808305859613)
              ·
                refine ⟨7410303292125303114697355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19760808779000808305859613 7410303292125303114697355)
                ·
                  refine ⟨11115454938187954672046033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7410303292125303114697355 11115454938187954672046033)
                  ·
                    refine ⟨8336591203640966004034525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11115454938187954672046033 8336591203640966004034525)
                    ·
                      refine ⟨3126221701365362251512947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8336591203640966004034525 3126221701365362251512947)
                      ·
                        rfl

theorem cell23_6088295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_6088295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088295 prefixEnd_6088295 := by exact prefixLift 6088295
  have htrace : WordTrace (prefixWord ++ tailWord_6088295) baseStart_6088295 baseEnd_6088295 := by
    simpa [prefixWord, tailWord_6088295, baseEnd_6088295] using wordTrace_append hprefix tailTrace_6088295
  have hstable : (prefixWord ++ tailWord_6088295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088295).length < 2 ^ (prefixWord ++ tailWord_6088295).sum := by decide
  have hdescent : baseEnd_6088295 < baseStart_6088295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088298 : List Nat := [3, 1, 3, 2, 1, 4, 9]
def baseStart_6088298 : Nat := 118140960795 + 6088298 * 2 ^ 59
def prefixEnd_6088298 : Nat := 4983230072969 + 3 ^ 40 * 6088298 * 2
def baseEnd_6088298 : Nat := 38595348664287972095993

theorem tailTrace_6088298 : CollatzResearch.WordTrace tailWord_6088298 prefixEnd_6088298 38595348664287972095993 := by
  unfold tailWord_6088298
  simp only [CollatzResearch.WordTrace]
  refine ⟨55514617724285904840230387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148038980598095746240614365 55514617724285904840230387)
  ·
    refine ⟨83271926586428857260345581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55514617724285904840230387 83271926586428857260345581)
    ·
      refine ⟨31226972469910821472629593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83271926586428857260345581 31226972469910821472629593)
      ·
        refine ⟨23420229352433116104472195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31226972469910821472629593 23420229352433116104472195)
        ·
          refine ⟨35130344028649674156708293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23420229352433116104472195 35130344028649674156708293)
          ·
            refine ⟨6586939505371813904382805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35130344028649674156708293 6586939505371813904382805)
            ·
              refine ⟨38595348664287972095993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6586939505371813904382805 38595348664287972095993)
              ·
                rfl

theorem cell23_6088298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 9].length) (baseStart_6088298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088298 prefixEnd_6088298 := by exact prefixLift 6088298
  have htrace : WordTrace (prefixWord ++ tailWord_6088298) baseStart_6088298 baseEnd_6088298 := by
    simpa [prefixWord, tailWord_6088298, baseEnd_6088298] using wordTrace_append hprefix tailTrace_6088298
  have hstable : (prefixWord ++ tailWord_6088298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088298).length < 2 ^ (prefixWord ++ tailWord_6088298).sum := by decide
  have hdescent : baseEnd_6088298 < baseStart_6088298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088309 : List Nat := [1, 3, 4, 2, 1, 1, 3, 1, 3, 2, 2]
def baseStart_6088309 : Nat := 118140960795 + 6088309 * 2 ^ 59
def prefixEnd_6088309 : Nat := 4983230072969 + 3 ^ 40 * 6088309 * 2
def baseEnd_6088309 : Nat := 3126228890094525196737883

theorem tailTrace_6088309 : CollatzResearch.WordTrace tailWord_6088309 prefixEnd_6088309 3126228890094525196737883 := by
  unfold tailWord_6088309
  simp only [CollatzResearch.WordTrace]
  refine ⟨222058872100103768239571981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148039248066735845493047987 222058872100103768239571981)
  ·
    refine ⟨83272077037538913089839493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222058872100103768239571981 83272077037538913089839493)
    ·
      refine ⟨15613514444538546204344905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83272077037538913089839493 15613514444538546204344905)
      ·
        refine ⟨11710135833403909653258679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15613514444538546204344905 11710135833403909653258679)
        ·
          refine ⟨17565203750105864479888019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11710135833403909653258679 17565203750105864479888019)
          ·
            refine ⟨26347805625158796719832029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17565203750105864479888019 26347805625158796719832029)
            ·
              refine ⟨9880427109434548769937011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26347805625158796719832029 9880427109434548769937011)
              ·
                refine ⟨14820640664151823154905517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9880427109434548769937011 14820640664151823154905517)
                ·
                  refine ⟨5557740249056933683089569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14820640664151823154905517 5557740249056933683089569)
                  ·
                    refine ⟨4168305186792700262317177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5557740249056933683089569 4168305186792700262317177)
                    ·
                      refine ⟨3126228890094525196737883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4168305186792700262317177 3126228890094525196737883)
                      ·
                        rfl

theorem cell23_6088309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_6088309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088309 prefixEnd_6088309 := by exact prefixLift 6088309
  have htrace : WordTrace (prefixWord ++ tailWord_6088309) baseStart_6088309 baseEnd_6088309 := by
    simpa [prefixWord, tailWord_6088309, baseEnd_6088309] using wordTrace_append hprefix tailTrace_6088309
  have hstable : (prefixWord ++ tailWord_6088309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088309).length < 2 ^ (prefixWord ++ tailWord_6088309).sum := by decide
  have hdescent : baseEnd_6088309 < baseStart_6088309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088311 : List Nat := [1, 1, 3, 1, 1, 3, 1, 3, 2, 7]
def baseStart_6088311 : Nat := 118140960795 + 6088311 * 2 ^ 59
def prefixEnd_6088311 : Nat := 4983230072969 + 3 ^ 40 * 6088311 * 2
def baseEnd_6088311 : Nat := 1042076639018611396304291

theorem tailTrace_6088311 : CollatzResearch.WordTrace tailWord_6088311 prefixEnd_6088311 1042076639018611396304291 := by
  unfold tailWord_6088311
  simp only [CollatzResearch.WordTrace]
  refine ⟨222058945046096522581144787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148039296697397681720763191 222058945046096522581144787)
  ·
    refine ⟨333088417569144783871717181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222058945046096522581144787 333088417569144783871717181)
    ·
      refine ⟨124908156588429293951893943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 333088417569144783871717181 124908156588429293951893943)
      ·
        refine ⟨187362234882643940927840915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124908156588429293951893943 187362234882643940927840915)
        ·
          refine ⟨281043352323965911391761373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187362234882643940927840915 281043352323965911391761373)
          ·
            refine ⟨105391257121487216771910515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 281043352323965911391761373 105391257121487216771910515)
            ·
              refine ⟨158086885682230825157865773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105391257121487216771910515 158086885682230825157865773)
              ·
                refine ⟨59282582130836559434199665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158086885682230825157865773 59282582130836559434199665)
                ·
                  refine ⟨44461936598127419575649749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59282582130836559434199665 44461936598127419575649749)
                  ·
                    refine ⟨1042076639018611396304291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44461936598127419575649749 1042076639018611396304291)
                    ·
                      rfl

theorem cell23_6088311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 2, 7].length) (baseStart_6088311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088311 prefixEnd_6088311 := by exact prefixLift 6088311
  have htrace : WordTrace (prefixWord ++ tailWord_6088311) baseStart_6088311 baseEnd_6088311 := by
    simpa [prefixWord, tailWord_6088311, baseEnd_6088311] using wordTrace_append hprefix tailTrace_6088311
  have hstable : (prefixWord ++ tailWord_6088311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088311).length < 2 ^ (prefixWord ++ tailWord_6088311).sum := by decide
  have hdescent : baseEnd_6088311 < baseStart_6088311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088360 : List Nat := [2, 1, 7, 1, 1, 1, 1, 4, 1, 2, 2]
def baseStart_6088360 : Nat := 118140960795 + 6088360 * 2 ^ 59
def prefixEnd_6088360 : Nat := 4983230072969 + 3 ^ 40 * 6088360 * 2
def baseEnd_6088360 : Nat := 3126255077607904497200149

theorem tailTrace_6088360 : CollatzResearch.WordTrace tailWord_6088360 prefixEnd_6088360 3126255077607904497200149 := by
  unfold tailWord_6088360
  simp only [CollatzResearch.WordTrace]
  refine ⟨111030366111459501974839267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148040488148612669299785689 111030366111459501974839267)
  ·
    refine ⟨166545549167189252962258901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111030366111459501974839267 166545549167189252962258901)
    ·
      refine ⟨3903411308605998116302943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 166545549167189252962258901 3903411308605998116302943)
      ·
        refine ⟨5855116962908997174454415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3903411308605998116302943 5855116962908997174454415)
        ·
          refine ⟨8782675444363495761681623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5855116962908997174454415 8782675444363495761681623)
          ·
            refine ⟨13174013166545243642522435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8782675444363495761681623 13174013166545243642522435)
            ·
              refine ⟨19761019749817865463783653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13174013166545243642522435 19761019749817865463783653)
              ·
                refine ⟨3705191203090849774459435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19761019749817865463783653 3705191203090849774459435)
                ·
                  refine ⟨5557786804636274661689153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3705191203090849774459435 5557786804636274661689153)
                  ·
                    refine ⟨4168340103477205996266865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5557786804636274661689153 4168340103477205996266865)
                    ·
                      refine ⟨3126255077607904497200149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4168340103477205996266865 3126255077607904497200149)
                      ·
                        rfl

theorem cell23_6088360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_6088360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088360 prefixEnd_6088360 := by exact prefixLift 6088360
  have htrace : WordTrace (prefixWord ++ tailWord_6088360) baseStart_6088360 baseEnd_6088360 := by
    simpa [prefixWord, tailWord_6088360, baseEnd_6088360] using wordTrace_append hprefix tailTrace_6088360
  have hstable : (prefixWord ++ tailWord_6088360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088360).length < 2 ^ (prefixWord ++ tailWord_6088360).sum := by decide
  have hdescent : baseEnd_6088360 < baseStart_6088360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088368 : List Nat := [2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 3]
def baseStart_6088368 : Nat := 118140960795 + 6088368 * 2 ^ 59
def prefixEnd_6088368 : Nat := 4983230072969 + 3 ^ 40 * 6088368 * 2
def baseEnd_6088368 : Nat := 3126259185453140465900111

theorem tailTrace_6088368 : CollatzResearch.WordTrace tailWord_6088368 prefixEnd_6088368 3126259185453140465900111 := by
  unfold tailWord_6088368
  simp only [CollatzResearch.WordTrace]
  refine ⟨111030512003445010657984879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148040682671260014210646505 111030512003445010657984879)
  ·
    refine ⟨166545768005167515986977319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111030512003445010657984879 166545768005167515986977319)
    ·
      refine ⟨249818652007751273980465979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166545768005167515986977319 249818652007751273980465979)
      ·
        refine ⟨374727978011626910970698969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249818652007751273980465979 374727978011626910970698969)
        ·
          refine ⟨281045983508720183228024227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374727978011626910970698969 281045983508720183228024227)
          ·
            refine ⟨421568975263080274842036341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281045983508720183228024227 421568975263080274842036341)
            ·
              refine ⟨39522091430913775766440907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 421568975263080274842036341 39522091430913775766440907)
              ·
                refine ⟨59283137146370663649661361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39522091430913775766440907 59283137146370663649661361)
                ·
                  refine ⟨44462352859777997737246021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59283137146370663649661361 44462352859777997737246021)
                  ·
                    refine ⟨8336691161208374575733629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44462352859777997737246021 8336691161208374575733629)
                    ·
                      refine ⟨3126259185453140465900111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8336691161208374575733629 3126259185453140465900111)
                      ·
                        rfl

theorem cell23_6088368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 3].length) (baseStart_6088368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088368 prefixEnd_6088368 := by exact prefixLift 6088368
  have htrace : WordTrace (prefixWord ++ tailWord_6088368) baseStart_6088368 baseEnd_6088368 := by
    simpa [prefixWord, tailWord_6088368, baseEnd_6088368] using wordTrace_append hprefix tailTrace_6088368
  have hstable : (prefixWord ++ tailWord_6088368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088368).length < 2 ^ (prefixWord ++ tailWord_6088368).sum := by decide
  have hdescent : baseEnd_6088368 < baseStart_6088368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088378 : List Nat := [3, 1, 1, 1, 2, 4, 1, 1, 1, 4, 4]
def baseStart_6088378 : Nat := 118140960795 + 6088378 * 2 ^ 59
def prefixEnd_6088378 : Nat := 4983230072969 + 3 ^ 40 * 6088378 * 2
def baseEnd_6088378 : Nat := 3126264320259685426775065

theorem tailTrace_6088378 : CollatzResearch.WordTrace tailWord_6088378 prefixEnd_6088378 3126264320259685426775065 := by
  unfold tailWord_6088378
  simp only [CollatzResearch.WordTrace]
  refine ⟨55515347184213448255958447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148040925824569195349222525 55515347184213448255958447)
  ·
    refine ⟨83273020776320172383937671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55515347184213448255958447 83273020776320172383937671)
    ·
      refine ⟨124909531164480258575906507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83273020776320172383937671 124909531164480258575906507)
      ·
        refine ⟨187364296746720387863859761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124909531164480258575906507 187364296746720387863859761)
        ·
          refine ⟨140523222560040290897894821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187364296746720387863859761 140523222560040290897894821)
          ·
            refine ⟨26348104230007554543355279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140523222560040290897894821 26348104230007554543355279)
            ·
              refine ⟨39522156345011331815032919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26348104230007554543355279 39522156345011331815032919)
              ·
                refine ⟨59283234517516997722549379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39522156345011331815032919 59283234517516997722549379)
                ·
                  refine ⟨88924851776275496583824069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59283234517516997722549379 88924851776275496583824069)
                  ·
                    refine ⟨16673409708051655609467013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 88924851776275496583824069 16673409708051655609467013)
                    ·
                      refine ⟨3126264320259685426775065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16673409708051655609467013 3126264320259685426775065)
                      ·
                        rfl

theorem cell23_6088378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 1, 4, 4].length) (baseStart_6088378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088378 prefixEnd_6088378 := by exact prefixLift 6088378
  have htrace : WordTrace (prefixWord ++ tailWord_6088378) baseStart_6088378 baseEnd_6088378 := by
    simpa [prefixWord, tailWord_6088378, baseEnd_6088378] using wordTrace_append hprefix tailTrace_6088378
  have hstable : (prefixWord ++ tailWord_6088378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088378).length < 2 ^ (prefixWord ++ tailWord_6088378).sum := by decide
  have hdescent : baseEnd_6088378 < baseStart_6088378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088382 : List Nat := [4, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2]
def baseStart_6088382 : Nat := 118140960795 + 6088382 * 2 ^ 59
def prefixEnd_6088382 : Nat := 4983230072969 + 3 ^ 40 * 6088382 * 2
def baseEnd_6088382 : Nat := 3126266374182303411125047

theorem tailTrace_6088382 : CollatzResearch.WordTrace tailWord_6088382 prefixEnd_6088382 3126266374182303411125047 := by
  unfold tailWord_6088382
  simp only [CollatzResearch.WordTrace]
  refine ⟨27757691828604912713372425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148041023085892867804652933 27757691828604912713372425)
  ·
    refine ⟨20818268871453684535029319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27757691828604912713372425 20818268871453684535029319)
    ·
      refine ⟨31227403307180526802543979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20818268871453684535029319 31227403307180526802543979)
      ·
        refine ⟨46841104960770790203815969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31227403307180526802543979 46841104960770790203815969)
        ·
          refine ⟨35130828720578092652861977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46841104960770790203815969 35130828720578092652861977)
          ·
            refine ⟨26348121540433569489646483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35130828720578092652861977 26348121540433569489646483)
            ·
              refine ⟨39522182310650354234469725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26348121540433569489646483 39522182310650354234469725)
              ·
                refine ⟨14820818366493882837926147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39522182310650354234469725 14820818366493882837926147)
                ·
                  refine ⟨22231227549740824256889221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14820818366493882837926147 22231227549740824256889221)
                  ·
                    refine ⟨4168355165576404548166729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22231227549740824256889221 4168355165576404548166729)
                    ·
                      refine ⟨3126266374182303411125047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4168355165576404548166729 3126266374182303411125047)
                      ·
                        rfl

theorem cell23_6088382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_6088382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088382 prefixEnd_6088382 := by exact prefixLift 6088382
  have htrace : WordTrace (prefixWord ++ tailWord_6088382) baseStart_6088382 baseEnd_6088382 := by
    simpa [prefixWord, tailWord_6088382, baseEnd_6088382] using wordTrace_append hprefix tailTrace_6088382
  have hstable : (prefixWord ++ tailWord_6088382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088382).length < 2 ^ (prefixWord ++ tailWord_6088382).sum := by decide
  have hdescent : baseEnd_6088382 < baseStart_6088382 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088428 : List Nat := [2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 5]
def baseStart_6088428 : Nat := 118140960795 + 6088428 * 2 ^ 59
def prefixEnd_6088428 : Nat := 4983230072969 + 3 ^ 40 * 6088428 * 2
def baseEnd_6088428 : Nat := 3126289994292410231149835

theorem tailTrace_6088428 : CollatzResearch.WordTrace tailWord_6088428 prefixEnd_6088428 3126289994292410231149835 := by
  unfold tailWord_6088428
  simp only [CollatzResearch.WordTrace]
  refine ⟨111031606193336325781576969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148042141591115101042102625 111031606193336325781576969)
  ·
    refine ⟨83273704645002244336182727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111031606193336325781576969 83273704645002244336182727)
    ·
      refine ⟨124910556967503366504274091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83273704645002244336182727 124910556967503366504274091)
      ·
        refine ⟨187365835451255049756411137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124910556967503366504274091 187365835451255049756411137)
        ·
          refine ⟨140524376588441287317308353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187365835451255049756411137 140524376588441287317308353)
          ·
            refine ⟨105393282441330965487981265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140524376588441287317308353 105393282441330965487981265)
            ·
              refine ⟨79044961830998224115985949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105393282441330965487981265 79044961830998224115985949)
              ·
                refine ⟨29641860686624334043494731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79044961830998224115985949 29641860686624334043494731)
                ·
                  refine ⟨44462791029936501065242097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29641860686624334043494731 44462791029936501065242097)
                  ·
                    refine ⟨33347093272452375798931573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44462791029936501065242097 33347093272452375798931573)
                    ·
                      refine ⟨3126289994292410231149835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33347093272452375798931573 3126289994292410231149835)
                      ·
                        rfl

theorem cell23_6088428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 5].length) (baseStart_6088428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088428 prefixEnd_6088428 := by exact prefixLift 6088428
  have htrace : WordTrace (prefixWord ++ tailWord_6088428) baseStart_6088428 baseEnd_6088428 := by
    simpa [prefixWord, tailWord_6088428, baseEnd_6088428] using wordTrace_append hprefix tailTrace_6088428
  have hstable : (prefixWord ++ tailWord_6088428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088428).length < 2 ^ (prefixWord ++ tailWord_6088428).sum := by decide
  have hdescent : baseEnd_6088428 < baseStart_6088428 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088475 : List Nat := [1, 1, 1, 1, 1, 1, 4, 6, 2, 2, 3]
def baseStart_6088475 : Nat := 118140960795 + 6088475 * 2 ^ 59
def prefixEnd_6088475 : Nat := 4983230072969 + 3 ^ 40 * 6088475 * 2
def baseEnd_6088475 : Nat := 3126314127883171547262119

theorem tailTrace_6088475 : CollatzResearch.WordTrace tailWord_6088475 prefixEnd_6088475 3126314127883171547262119 := by
  unfold tailWord_6088475
  simp only [CollatzResearch.WordTrace]
  refine ⟨222064926617502378590114879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148043284411668252393409919 222064926617502378590114879)
  ·
    refine ⟨333097389926253567885172319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222064926617502378590114879 333097389926253567885172319)
    ·
      refine ⟨499646084889380351827758479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333097389926253567885172319 499646084889380351827758479)
      ·
        refine ⟨749469127334070527741637719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 499646084889380351827758479 749469127334070527741637719)
        ·
          refine ⟨1124203691001105791612456579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 749469127334070527741637719 1124203691001105791612456579)
          ·
            refine ⟨1686305536501658687418684869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1124203691001105791612456579 1686305536501658687418684869)
            ·
              refine ⟨316182288094061003891003413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1686305536501658687418684869 316182288094061003891003413)
              ·
                refine ⟨14821044754409109557390785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 316182288094061003891003413 14821044754409109557390785)
                ·
                  refine ⟨11115783565806832168043089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14821044754409109557390785 11115783565806832168043089)
                  ·
                    refine ⟨8336837674355124126032317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11115783565806832168043089 8336837674355124126032317)
                    ·
                      refine ⟨3126314127883171547262119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8336837674355124126032317 3126314127883171547262119)
                      ·
                        rfl

theorem cell23_6088475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 2, 3].length) (baseStart_6088475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088475 prefixEnd_6088475 := by exact prefixLift 6088475
  have htrace : WordTrace (prefixWord ++ tailWord_6088475) baseStart_6088475 baseEnd_6088475 := by
    simpa [prefixWord, tailWord_6088475, baseEnd_6088475] using wordTrace_append hprefix tailTrace_6088475
  have hstable : (prefixWord ++ tailWord_6088475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088475).length < 2 ^ (prefixWord ++ tailWord_6088475).sum := by decide
  have hdescent : baseEnd_6088475 < baseStart_6088475 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088509 : List Nat := [1, 4, 1, 4, 1, 2, 2, 1, 2, 2, 3]
def baseStart_6088509 : Nat := 118140960795 + 6088509 * 2 ^ 59
def prefixEnd_6088509 : Nat := 4983230072969 + 3 ^ 40 * 6088509 * 2
def baseEnd_6088509 : Nat := 3126331586225424414236963

theorem tailTrace_6088509 : CollatzResearch.WordTrace tailWord_6088509 prefixEnd_6088509 3126331586225424414236963 := by
  unfold tailWord_6088509
  simp only [CollatzResearch.WordTrace]
  refine ⟨222066166699379202396852581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148044111132919468264568387 222066166699379202396852581)
  ·
    refine ⟨41637406256133600449409859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222066166699379202396852581 41637406256133600449409859)
    ·
      refine ⟨62456109384200400674114789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41637406256133600449409859 62456109384200400674114789)
      ·
        refine ⟨11710520509537575126396523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62456109384200400674114789 11710520509537575126396523)
        ·
          refine ⟨17565780764306362689594785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11710520509537575126396523 17565780764306362689594785)
          ·
            refine ⟨13174335573229772017196089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17565780764306362689594785 13174335573229772017196089)
            ·
              refine ⟨9880751679922329012897067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13174335573229772017196089 9880751679922329012897067)
              ·
                refine ⟨14821127519883493519345601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9880751679922329012897067 14821127519883493519345601)
                ·
                  refine ⟨11115845639912620139509201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14821127519883493519345601 11115845639912620139509201)
                  ·
                    refine ⟨8336884229934465104631901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11115845639912620139509201 8336884229934465104631901)
                    ·
                      refine ⟨3126331586225424414236963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8336884229934465104631901 3126331586225424414236963)
                      ·
                        rfl

theorem cell23_6088509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_6088509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088509 prefixEnd_6088509 := by exact prefixLift 6088509
  have htrace : WordTrace (prefixWord ++ tailWord_6088509) baseStart_6088509 baseEnd_6088509 := by
    simpa [prefixWord, tailWord_6088509, baseEnd_6088509] using wordTrace_append hprefix tailTrace_6088509
  have hstable : (prefixWord ++ tailWord_6088509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088509).length < 2 ^ (prefixWord ++ tailWord_6088509).sum := by decide
  have hdescent : baseEnd_6088509 < baseStart_6088509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088545 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 5, 1, 4]
def baseStart_6088545 : Nat := 118140960795 + 6088545 * 2 ^ 59
def prefixEnd_6088545 : Nat := 4983230072969 + 3 ^ 40 * 6088545 * 2
def baseEnd_6088545 : Nat := 3126350071528986273386797

theorem tailTrace_6088545 : CollatzResearch.WordTrace tailWord_6088545 prefixEnd_6088545 3126350071528986273386797 := by
  unfold tailWord_6088545
  simp only [CollatzResearch.WordTrace]
  refine ⟨222067479727248780545163089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148044986484832520363442059 222067479727248780545163089)
  ·
    refine ⟨166550609795436585408872317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222067479727248780545163089 166550609795436585408872317)
    ·
      refine ⟨62456478673288719528327119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166550609795436585408872317 62456478673288719528327119)
      ·
        refine ⟨93684718009933079292490679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62456478673288719528327119 93684718009933079292490679)
        ·
          refine ⟨140527077014899618938736019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93684718009933079292490679 140527077014899618938736019)
          ·
            refine ⟨210790615522349428408104029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140527077014899618938736019 210790615522349428408104029)
            ·
              refine ⟨79046480820881035653039011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 210790615522349428408104029 79046480820881035653039011)
              ·
                refine ⟨118569721231321553479558517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79046480820881035653039011 118569721231321553479558517)
                ·
                  refine ⟨11115911365436395638708611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 118569721231321553479558517 11115911365436395638708611)
                  ·
                    refine ⟨16673867048154593458062917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11115911365436395638708611 16673867048154593458062917)
                    ·
                      refine ⟨3126350071528986273386797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16673867048154593458062917 3126350071528986273386797)
                      ·
                        rfl

theorem cell23_6088545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_6088545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088545 prefixEnd_6088545 := by exact prefixLift 6088545
  have htrace : WordTrace (prefixWord ++ tailWord_6088545) baseStart_6088545 baseEnd_6088545 := by
    simpa [prefixWord, tailWord_6088545, baseEnd_6088545] using wordTrace_append hprefix tailTrace_6088545
  have hstable : (prefixWord ++ tailWord_6088545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088545).length < 2 ^ (prefixWord ++ tailWord_6088545).sum := by decide
  have hdescent : baseEnd_6088545 < baseStart_6088545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088555 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 6, 4]
def baseStart_6088555 : Nat := 118140960795 + 6088555 * 2 ^ 59
def prefixEnd_6088555 : Nat := 4983230072969 + 3 ^ 40 * 6088555 * 2
def baseEnd_6088555 : Nat := 1042118402111843744753917

theorem tailTrace_6088555 : CollatzResearch.WordTrace tailWord_6088555 prefixEnd_6088555 1042118402111843744753917 := by
  unfold tailWord_6088555
  simp only [CollatzResearch.WordTrace]
  refine ⟨222067844457212552253027119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148045229638141701502018079 222067844457212552253027119)
  ·
    refine ⟨333101766685818828379540679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222067844457212552253027119 333101766685818828379540679)
    ·
      refine ⟨499652650028728242569311019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333101766685818828379540679 499652650028728242569311019)
      ·
        refine ⟨749478975043092363853966529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 499652650028728242569311019 749478975043092363853966529)
        ·
          refine ⟨562109231282319272890474897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 749478975043092363853966529 562109231282319272890474897)
          ·
            refine ⟨421581923461739454667856173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 562109231282319272890474897 421581923461739454667856173)
            ·
              refine ⟨158093221298152295500446065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 421581923461739454667856173 158093221298152295500446065)
              ·
                refine ⟨118569915973614221625334549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158093221298152295500446065 118569915973614221625334549)
                ·
                  refine ⟨5557964811263166638687557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 118569915973614221625334549 5557964811263166638687557)
                  ·
                    refine ⟨1042118402111843744753917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5557964811263166638687557 1042118402111843744753917)
                    ·
                      rfl

theorem cell23_6088555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 6, 4].length) (baseStart_6088555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088555 prefixEnd_6088555 := by exact prefixLift 6088555
  have htrace : WordTrace (prefixWord ++ tailWord_6088555) baseStart_6088555 baseEnd_6088555 := by
    simpa [prefixWord, tailWord_6088555, baseEnd_6088555] using wordTrace_append hprefix tailTrace_6088555
  have hstable : (prefixWord ++ tailWord_6088555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088555).length < 2 ^ (prefixWord ++ tailWord_6088555).sum := by decide
  have hdescent : baseEnd_6088555 < baseStart_6088555 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088562 : List Nat := [3, 2, 1, 2, 1, 1, 1, 6, 1, 1, 4]
def baseStart_6088562 : Nat := 118140960795 + 6088562 * 2 ^ 59
def prefixEnd_6088562 : Nat := 4983230072969 + 3 ^ 40 * 6088562 * 2
def baseEnd_6088562 : Nat := 3126358800700112706874219

theorem tailTrace_6088562 : CollatzResearch.WordTrace tailWord_6088562 prefixEnd_6088562 3126358800700112706874219 := by
  unfold tailWord_6088562
  simp only [CollatzResearch.WordTrace]
  refine ⟨55517024942046798112132985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148045399845458128299021293 55517024942046798112132985)
  ·
    refine ⟨41637768706535098584099739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55517024942046798112132985 41637768706535098584099739)
    ·
      refine ⟨62456653059802647876149609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41637768706535098584099739 62456653059802647876149609)
      ·
        refine ⟨46842489794851985907112207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62456653059802647876149609 46842489794851985907112207)
        ·
          refine ⟨70263734692277978860668311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46842489794851985907112207 70263734692277978860668311)
          ·
            refine ⟨105395602038416968291002467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70263734692277978860668311 105395602038416968291002467)
            ·
              refine ⟨158093403057625452436503701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105395602038416968291002467 158093403057625452436503701)
              ·
                refine ⟨7410628268326193082961111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 158093403057625452436503701 7410628268326193082961111)
                ·
                  refine ⟨11115942402489289624441667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7410628268326193082961111 11115942402489289624441667)
                  ·
                    refine ⟨16673913603733934436662501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11115942402489289624441667 16673913603733934436662501)
                    ·
                      refine ⟨3126358800700112706874219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16673913603733934436662501 3126358800700112706874219)
                      ·
                        rfl

theorem cell23_6088562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_6088562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088562 prefixEnd_6088562 := by exact prefixLift 6088562
  have htrace : WordTrace (prefixWord ++ tailWord_6088562) baseStart_6088562 baseEnd_6088562 := by
    simpa [prefixWord, tailWord_6088562, baseEnd_6088562] using wordTrace_append hprefix tailTrace_6088562
  have hstable : (prefixWord ++ tailWord_6088562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088562).length < 2 ^ (prefixWord ++ tailWord_6088562).sum := by decide
  have hdescent : baseEnd_6088562 < baseStart_6088562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088566 : List Nat := [5, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2]
def baseStart_6088566 : Nat := 118140960795 + 6088566 * 2 ^ 59
def prefixEnd_6088566 : Nat := 4983230072969 + 3 ^ 40 * 6088566 * 2
def baseEnd_6088566 : Nat := 3126360854622730691224201

theorem tailTrace_6088566 : CollatzResearch.WordTrace tailWord_6088566 prefixEnd_6088566 3126360854622730691224201 := by
  unfold tailWord_6088566
  simp only [CollatzResearch.WordTrace]
  refine ⟨13879265353760793820729847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148045497106781800754451701 13879265353760793820729847)
  ·
    refine ⟨20818898030641190731094771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13879265353760793820729847 20818898030641190731094771)
    ·
      refine ⟨31228347045961786096642157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20818898030641190731094771 31228347045961786096642157)
      ·
        refine ⟨11710630142235669786240809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31228347045961786096642157 11710630142235669786240809)
        ·
          refine ⟨8782972606676752339680607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11710630142235669786240809 8782972606676752339680607)
          ·
            refine ⟨13174458910015128509520911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8782972606676752339680607 13174458910015128509520911)
            ·
              refine ⟨19761688365022692764281367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13174458910015128509520911 19761688365022692764281367)
              ·
                refine ⟨29642532547534039146422051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19761688365022692764281367 29642532547534039146422051)
                ·
                  refine ⟨44463798821301058719633077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29642532547534039146422051 44463798821301058719633077)
                  ·
                    refine ⟨4168481139496974254965601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44463798821301058719633077 4168481139496974254965601)
                    ·
                      refine ⟨3126360854622730691224201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4168481139496974254965601 3126360854622730691224201)
                      ·
                        rfl

theorem cell23_6088566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_6088566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088566 prefixEnd_6088566 := by exact prefixLift 6088566
  have htrace : WordTrace (prefixWord ++ tailWord_6088566) baseStart_6088566 baseEnd_6088566 := by
    simpa [prefixWord, tailWord_6088566, baseEnd_6088566] using wordTrace_append hprefix tailTrace_6088566
  have hstable : (prefixWord ++ tailWord_6088566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088566).length < 2 ^ (prefixWord ++ tailWord_6088566).sum := by decide
  have hdescent : baseEnd_6088566 < baseStart_6088566 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088579 : List Nat := [1, 1, 1, 3, 4, 2, 4, 1, 1, 1, 4]
def baseStart_6088579 : Nat := 118140960795 + 6088579 * 2 ^ 59
def prefixEnd_6088579 : Nat := 4983230072969 + 3 ^ 40 * 6088579 * 2
def baseEnd_6088579 : Nat := 3126367529871239140361641

theorem tailTrace_6088579 : CollatzResearch.WordTrace tailWord_6088579 prefixEnd_6088579 3126367529871239140361641 := by
  unfold tailWord_6088579
  simp only [CollatzResearch.WordTrace]
  refine ⟨222068719809125604351900791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148045813206083736234600527 222068719809125604351900791)
  ·
    refine ⟨333103079713688406527851187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222068719809125604351900791 333103079713688406527851187)
    ·
      refine ⟨499654619570532609791776781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333103079713688406527851187 499654619570532609791776781)
      ·
        refine ⟨187370482338949728671916293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 499654619570532609791776781 187370482338949728671916293)
        ·
          refine ⟨35131965438553074125984305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 187370482338949728671916293 35131965438553074125984305)
          ·
            refine ⟨26348974078914805594488229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35131965438553074125984305 26348974078914805594488229)
            ·
              refine ⟨4940432639796526048966543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26348974078914805594488229 4940432639796526048966543)
              ·
                refine ⟨7410648959694789073449815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4940432639796526048966543 7410648959694789073449815)
                ·
                  refine ⟨11115973439542183610174723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7410648959694789073449815 11115973439542183610174723)
                  ·
                    refine ⟨16673960159313275415262085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11115973439542183610174723 16673960159313275415262085)
                    ·
                      refine ⟨3126367529871239140361641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16673960159313275415262085 3126367529871239140361641)
                      ·
                        rfl

theorem cell23_6088579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 1, 1, 4].length) (baseStart_6088579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088579 prefixEnd_6088579 := by exact prefixLift 6088579
  have htrace : WordTrace (prefixWord ++ tailWord_6088579) baseStart_6088579 baseEnd_6088579 := by
    simpa [prefixWord, tailWord_6088579, baseEnd_6088579] using wordTrace_append hprefix tailTrace_6088579
  have hstable : (prefixWord ++ tailWord_6088579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088579).length < 2 ^ (prefixWord ++ tailWord_6088579).sum := by decide
  have hdescent : baseEnd_6088579 < baseStart_6088579 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088596 : List Nat := [2, 4, 2, 1, 1, 2, 1, 3, 3, 2, 2]
def baseStart_6088596 : Nat := 118140960795 + 6088596 * 2 ^ 59
def prefixEnd_6088596 : Nat := 4983230072969 + 3 ^ 40 * 6088596 * 2
def baseEnd_6088596 : Nat := 3126376259042365573849063

theorem tailTrace_6088596 : CollatzResearch.WordTrace tailWord_6088596 prefixEnd_6088596 3126376259042365573849063 := by
  unfold tailWord_6088596
  simp only [CollatzResearch.WordTrace]
  refine ⟨111034669925032008127634821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148046226566709344170179761 111034669925032008127634821)
  ·
    refine ⟨20819000610943501523931529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111034669925032008127634821 20819000610943501523931529)
    ·
      refine ⟨15614250458207626142948647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20819000610943501523931529 15614250458207626142948647)
      ·
        refine ⟨23421375687311439214422971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15614250458207626142948647 23421375687311439214422971)
        ·
          refine ⟨35132063530967158821634457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23421375687311439214422971 35132063530967158821634457)
          ·
            refine ⟨26349047648225369116225843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35132063530967158821634457 26349047648225369116225843)
            ·
              refine ⟨39523571472338053674338765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26349047648225369116225843 39523571472338053674338765)
              ·
                refine ⟨14821339302126770127877037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39523571472338053674338765 14821339302126770127877037)
                ·
                  refine ⟨5558002238297538797953889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14821339302126770127877037 5558002238297538797953889)
                  ·
                    refine ⟨4168501678723154098465417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5558002238297538797953889 4168501678723154098465417)
                    ·
                      refine ⟨3126376259042365573849063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4168501678723154098465417 3126376259042365573849063)
                      ·
                        rfl

theorem cell23_6088596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_6088596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088596 prefixEnd_6088596 := by exact prefixLift 6088596
  have htrace : WordTrace (prefixWord ++ tailWord_6088596) baseStart_6088596 baseEnd_6088596 := by
    simpa [prefixWord, tailWord_6088596, baseEnd_6088596] using wordTrace_append hprefix tailTrace_6088596
  have hstable : (prefixWord ++ tailWord_6088596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088596).length < 2 ^ (prefixWord ++ tailWord_6088596).sum := by decide
  have hdescent : baseEnd_6088596 < baseStart_6088596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088629 : List Nat := [1, 3, 3, 2, 1, 2, 1, 2, 4, 1, 3]
def baseStart_6088629 : Nat := 118140960795 + 6088629 * 2 ^ 59
def prefixEnd_6088629 : Nat := 4983230072969 + 3 ^ 40 * 6088629 * 2
def baseEnd_6088629 : Nat := 3126393203903963944736411

theorem tailTrace_6088629 : CollatzResearch.WordTrace tailWord_6088629 prefixEnd_6088629 3126393203903963944736411 := by
  unfold tailWord_6088629
  simp only [CollatzResearch.WordTrace]
  refine ⟨222070543458944462891220941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148047028972629641927480627 222070543458944462891220941)
  ·
    refine ⟨83276453797104173584207853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222070543458944462891220941 83276453797104173584207853)
    ·
      refine ⟨31228670173914065094077945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83276453797104173584207853 31228670173914065094077945)
      ·
        refine ⟨23421502630435548820558459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31228670173914065094077945 23421502630435548820558459)
        ·
          refine ⟨35132253945653323230837689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23421502630435548820558459 35132253945653323230837689)
          ·
            refine ⟨26349190459239992423128267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35132253945653323230837689 26349190459239992423128267)
            ·
              refine ⟨39523785688859988634692401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26349190459239992423128267 39523785688859988634692401)
              ·
                refine ⟨29642839266644991476019301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39523785688859988634692401 29642839266644991476019301)
                ·
                  refine ⟨5558032362495935901753619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29642839266644991476019301 5558032362495935901753619)
                  ·
                    refine ⟨8337048543743903852630429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5558032362495935901753619 8337048543743903852630429)
                    ·
                      refine ⟨3126393203903963944736411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8337048543743903852630429 3126393203903963944736411)
                      ·
                        rfl

theorem cell23_6088629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_6088629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088629 prefixEnd_6088629 := by exact prefixLift 6088629
  have htrace : WordTrace (prefixWord ++ tailWord_6088629) baseStart_6088629 baseEnd_6088629 := by
    simpa [prefixWord, tailWord_6088629, baseEnd_6088629] using wordTrace_append hprefix tailTrace_6088629
  have hstable : (prefixWord ++ tailWord_6088629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088629).length < 2 ^ (prefixWord ++ tailWord_6088629).sum := by decide
  have hdescent : baseEnd_6088629 < baseStart_6088629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088639 : List Nat := [1, 1, 2, 2, 2, 1, 3, 5, 1, 3, 2]
def baseStart_6088639 : Nat := 118140960795 + 6088639 * 2 ^ 59
def prefixEnd_6088639 : Nat := 4983230072969 + 3 ^ 40 * 6088639 * 2
def baseEnd_6088639 : Nat := 3126398338710508905611365

theorem tailTrace_6088639 : CollatzResearch.WordTrace tailWord_6088639 prefixEnd_6088639 3126398338710508905611365 := by
  unfold tailWord_6088639
  simp only [CollatzResearch.WordTrace]
  refine ⟨222070908188908234599084971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148047272125938823066056647 222070908188908234599084971)
  ·
    refine ⟨333106362283362351898627457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222070908188908234599084971 333106362283362351898627457)
    ·
      refine ⟨249829771712521763923970593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333106362283362351898627457 249829771712521763923970593)
      ·
        refine ⟨187372328784391322942977945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249829771712521763923970593 187372328784391322942977945)
        ·
          refine ⟨140529246588293492207233459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187372328784391322942977945 140529246588293492207233459)
          ·
            refine ⟨210793869882440238310850189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140529246588293492207233459 210793869882440238310850189)
            ·
              refine ⟨79047701205915089366568821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 210793869882440238310850189 79047701205915089366568821)
              ·
                refine ⟨7410721988054539628115827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79047701205915089366568821 7410721988054539628115827)
                ·
                  refine ⟨11116082982081809442173741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7410721988054539628115827 11116082982081809442173741)
                  ·
                    refine ⟨4168531118280678540815153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11116082982081809442173741 4168531118280678540815153)
                    ·
                      refine ⟨3126398338710508905611365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4168531118280678540815153 3126398338710508905611365)
                      ·
                        rfl

theorem cell23_6088639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 1, 3, 2].length) (baseStart_6088639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088639 prefixEnd_6088639 := by exact prefixLift 6088639
  have htrace : WordTrace (prefixWord ++ tailWord_6088639) baseStart_6088639 baseEnd_6088639 := by
    simpa [prefixWord, tailWord_6088639, baseEnd_6088639] using wordTrace_append hprefix tailTrace_6088639
  have hstable : (prefixWord ++ tailWord_6088639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088639).length < 2 ^ (prefixWord ++ tailWord_6088639).sum := by decide
  have hdescent : baseEnd_6088639 < baseStart_6088639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088645 : List Nat := [1, 3, 1, 1, 1, 1, 1, 6, 2, 6]
def baseStart_6088645 : Nat := 118140960795 + 6088645 * 2 ^ 59
def prefixEnd_6088645 : Nat := 4983230072969 + 3 ^ 40 * 6088645 * 2
def baseEnd_6088645 : Nat := 1042133806531478627378779

theorem tailTrace_6088645 : CollatzResearch.WordTrace tailWord_6088645 prefixEnd_6088645 1042133806531478627378779 := by
  unfold tailWord_6088645
  simp only [CollatzResearch.WordTrace]
  refine ⟨222071127026886497623803389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148047418017924331749202259 222071127026886497623803389)
  ·
    refine ⟨83276672635082436608926271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222071127026886497623803389 83276672635082436608926271)
    ·
      refine ⟨124915008952623654913389407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83276672635082436608926271 124915008952623654913389407)
      ·
        refine ⟨187372513428935482370084111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124915008952623654913389407 187372513428935482370084111)
        ·
          refine ⟨281058770143403223555126167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187372513428935482370084111 281058770143403223555126167)
          ·
            refine ⟨421588155215104835332689251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281058770143403223555126167 421588155215104835332689251)
            ·
              refine ⟨632382232822657252999033877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 421588155215104835332689251 632382232822657252999033877)
              ·
                refine ⟨29642917163562058734329713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 632382232822657252999033877 29642917163562058734329713)
                ·
                  refine ⟨22232187872671544050747285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29642917163562058734329713 22232187872671544050747285)
                  ·
                    refine ⟨1042133806531478627378779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22232187872671544050747285 1042133806531478627378779)
                    ·
                      rfl

theorem cell23_6088645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 2, 6].length) (baseStart_6088645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088645 prefixEnd_6088645 := by exact prefixLift 6088645
  have htrace : WordTrace (prefixWord ++ tailWord_6088645) baseStart_6088645 baseEnd_6088645 := by
    simpa [prefixWord, tailWord_6088645, baseEnd_6088645] using wordTrace_append hprefix tailTrace_6088645
  have hstable : (prefixWord ++ tailWord_6088645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088645).length < 2 ^ (prefixWord ++ tailWord_6088645).sum := by decide
  have hdescent : baseEnd_6088645 < baseStart_6088645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088655 : List Nat := [1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 5]
def baseStart_6088655 : Nat := 118140960795 + 6088655 * 2 ^ 59
def prefixEnd_6088655 : Nat := 4983230072969 + 3 ^ 40 * 6088655 * 2
def baseEnd_6088655 : Nat := 3126406554400980843011291

theorem tailTrace_6088655 : CollatzResearch.WordTrace tailWord_6088655 prefixEnd_6088655 3126406554400980843011291 := by
  unfold tailWord_6088655
  simp only [CollatzResearch.WordTrace]
  refine ⟨222071491756850269331667419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148047661171233512887778279 222071491756850269331667419)
  ·
    refine ⟨333107237635275403997501129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222071491756850269331667419 333107237635275403997501129)
    ·
      refine ⟨249830428226456552998125847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333107237635275403997501129 249830428226456552998125847)
      ·
        refine ⟨374745642339684829497188771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249830428226456552998125847 374745642339684829497188771)
        ·
          refine ⟨562118463509527244245783157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374745642339684829497188771 562118463509527244245783157)
          ·
            refine ⟨52698605954018179148042171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 562118463509527244245783157 52698605954018179148042171)
            ·
              refine ⟨79047908931027268722063257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52698605954018179148042171 79047908931027268722063257)
              ·
                refine ⟨59285931698270451541547443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79047908931027268722063257 59285931698270451541547443)
                ·
                  refine ⟨88928897547405677312321165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59285931698270451541547443 88928897547405677312321165)
                  ·
                    refine ⟨33348336580277128992120437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88928897547405677312321165 33348336580277128992120437)
                    ·
                      refine ⟨3126406554400980843011291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33348336580277128992120437 3126406554400980843011291)
                      ·
                        rfl

theorem cell23_6088655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 5].length) (baseStart_6088655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088655 prefixEnd_6088655 := by exact prefixLift 6088655
  have htrace : WordTrace (prefixWord ++ tailWord_6088655) baseStart_6088655 baseEnd_6088655 := by
    simpa [prefixWord, tailWord_6088655, baseEnd_6088655] using wordTrace_append hprefix tailTrace_6088655
  have hstable : (prefixWord ++ tailWord_6088655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088655).length < 2 ^ (prefixWord ++ tailWord_6088655).sum := by decide
  have hdescent : baseEnd_6088655 < baseStart_6088655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088686 : List Nat := [4, 1, 2, 1, 3, 2, 1, 2, 1, 4, 2]
def baseStart_6088686 : Nat := 118140960795 + 6088686 * 2 ^ 59
def prefixEnd_6088686 : Nat := 4983230072969 + 3 ^ 40 * 6088686 * 2
def baseEnd_6088686 : Nat := 3126422472301270221723649

theorem tailTrace_6088686 : CollatzResearch.WordTrace tailWord_6088686 prefixEnd_6088686 3126422472301270221723649 := by
  unfold tailWord_6088686
  simp only [CollatzResearch.WordTrace]
  refine ⟨27759077802467245203255739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148048414946491974417363941 27759077802467245203255739)
  ·
    refine ⟨41638616703700867804883609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27759077802467245203255739 41638616703700867804883609)
    ·
      refine ⟨31228962527775650853662707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41638616703700867804883609 31228962527775650853662707)
      ·
        refine ⟨46843443791663476280494061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31228962527775650853662707 46843443791663476280494061)
        ·
          refine ⟨17566291421873803605185273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46843443791663476280494061 17566291421873803605185273)
          ·
            refine ⟨13174718566405352703888955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17566291421873803605185273 13174718566405352703888955)
            ·
              refine ⟨19762077849608029055833433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13174718566405352703888955 19762077849608029055833433)
              ·
                refine ⟨14821558387206021791875075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19762077849608029055833433 14821558387206021791875075)
                ·
                  refine ⟨22232337580809032687812613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14821558387206021791875075 22232337580809032687812613)
                  ·
                    refine ⟨4168563296401693628964865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22232337580809032687812613 4168563296401693628964865)
                    ·
                      refine ⟨3126422472301270221723649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4168563296401693628964865 3126422472301270221723649)
                      ·
                        rfl

theorem cell23_6088686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_6088686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088686 prefixEnd_6088686 := by exact prefixLift 6088686
  have htrace : WordTrace (prefixWord ++ tailWord_6088686) baseStart_6088686 baseEnd_6088686 := by
    simpa [prefixWord, tailWord_6088686, baseEnd_6088686] using wordTrace_append hprefix tailTrace_6088686
  have hstable : (prefixWord ++ tailWord_6088686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088686).length < 2 ^ (prefixWord ++ tailWord_6088686).sum := by decide
  have hdescent : baseEnd_6088686 < baseStart_6088686 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088709 : List Nat := [1, 3, 1, 1, 2, 5, 1, 4, 5]
def baseStart_6088709 : Nat := 118140960795 + 6088709 * 2 ^ 59
def prefixEnd_6088709 : Nat := 4983230072969 + 3 ^ 40 * 6088709 * 2
def baseEnd_6088709 : Nat := 347381586928480403526227

theorem tailTrace_6088709 : CollatzResearch.WordTrace tailWord_6088709 prefixEnd_6088709 347381586928480403526227 := by
  unfold tailWord_6088709
  simp only [CollatzResearch.WordTrace]
  refine ⟨222073461298654636554133181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148048974199103091036088787 222073461298654636554133181)
  ·
    refine ⟨83277547986995488707799943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222073461298654636554133181 83277547986995488707799943)
    ·
      refine ⟨124916321980493233061699915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83277547986995488707799943 124916321980493233061699915)
      ·
        refine ⟨187374482970739849592549873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124916321980493233061699915 187374482970739849592549873)
        ·
          refine ⟨140530862228054887194412405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187374482970739849592549873 140530862228054887194412405)
          ·
            refine ⟨13174768333880145674476163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 140530862228054887194412405 13174768333880145674476163)
            ·
              refine ⟨19762152500820218511714245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13174768333880145674476163 19762152500820218511714245)
              ·
                refine ⟨3705403593903790970946421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19762152500820218511714245 3705403593903790970946421)
                ·
                  refine ⟨347381586928480403526227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3705403593903790970946421 347381586928480403526227)
                  ·
                    rfl

theorem cell23_6088709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 4, 5].length) (baseStart_6088709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088709 prefixEnd_6088709 := by exact prefixLift 6088709
  have htrace : WordTrace (prefixWord ++ tailWord_6088709) baseStart_6088709 baseEnd_6088709 := by
    simpa [prefixWord, tailWord_6088709, baseEnd_6088709] using wordTrace_append hprefix tailTrace_6088709
  have hstable : (prefixWord ++ tailWord_6088709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088709).length < 2 ^ (prefixWord ++ tailWord_6088709).sum := by decide
  have hdescent : baseEnd_6088709 < baseStart_6088709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088743 : List Nat := [1, 1, 7, 1, 2, 1, 2, 3, 5]
def baseStart_6088743 : Nat := 118140960795 + 6088743 * 2 ^ 59
def prefixEnd_6088743 : Nat := 4983230072969 + 3 ^ 40 * 6088743 * 2
def baseEnd_6088743 : Nat := 347383526744286277634543

theorem tailTrace_6088743 : CollatzResearch.WordTrace tailWord_6088743 prefixEnd_6088743 347383526744286277634543 := by
  unfold tailWord_6088743
  simp only [CollatzResearch.WordTrace]
  refine ⟨222074701380531460360870883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148049800920354306907247255 222074701380531460360870883)
  ·
    refine ⟨333112052070797190541306325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222074701380531460360870883 333112052070797190541306325)
    ·
      refine ⟨7807313720409309153311867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 333112052070797190541306325 7807313720409309153311867)
      ·
        refine ⟨11710970580613963729967801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7807313720409309153311867 11710970580613963729967801)
        ·
          refine ⟨8783227935460472797475851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11710970580613963729967801 8783227935460472797475851)
          ·
            refine ⟨13174841903190709196213777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8783227935460472797475851 13174841903190709196213777)
            ·
              refine ⟨9881131427393031897160333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13174841903190709196213777 9881131427393031897160333)
              ·
                refine ⟨3705424285272386961435125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9881131427393031897160333 3705424285272386961435125)
                ·
                  refine ⟨347383526744286277634543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3705424285272386961435125 347383526744286277634543)
                  ·
                    rfl

theorem cell23_6088743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 3, 5].length) (baseStart_6088743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088743 prefixEnd_6088743 := by exact prefixLift 6088743
  have htrace : WordTrace (prefixWord ++ tailWord_6088743) baseStart_6088743 baseEnd_6088743 := by
    simpa [prefixWord, tailWord_6088743, baseEnd_6088743] using wordTrace_append hprefix tailTrace_6088743
  have hstable : (prefixWord ++ tailWord_6088743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088743).length < 2 ^ (prefixWord ++ tailWord_6088743).sum := by decide
  have hdescent : baseEnd_6088743 < baseStart_6088743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088759 : List Nat := [1, 1, 3, 1, 2, 2, 3, 2, 2, 4, 2]
def baseStart_6088759 : Nat := 118140960795 + 6088759 * 2 ^ 59
def prefixEnd_6088759 : Nat := 4983230072969 + 3 ^ 40 * 6088759 * 2
def baseEnd_6088759 : Nat := 3126459956389048436110813

theorem tailTrace_6088759 : CollatzResearch.WordTrace tailWord_6088759 prefixEnd_6088759 3126459956389048436110813 := by
  unfold tailWord_6088759
  simp only [CollatzResearch.WordTrace]
  refine ⟨222075284948473495093453331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148050189965648996728968887 222075284948473495093453331)
  ·
    refine ⟨333112927422710242640179997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222075284948473495093453331 333112927422710242640179997)
    ·
      refine ⟨124917347783516340990067499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 333112927422710242640179997 124917347783516340990067499)
      ·
        refine ⟨187376021675274511485101249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124917347783516340990067499 187376021675274511485101249)
        ·
          refine ⟨140532016256455883613825937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187376021675274511485101249 140532016256455883613825937)
          ·
            refine ⟨105399012192341912710369453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140532016256455883613825937 105399012192341912710369453)
            ·
              refine ⟨39524629572128217266388545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105399012192341912710369453 39524629572128217266388545)
              ·
                refine ⟨29643472179096162949791409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39524629572128217266388545 29643472179096162949791409)
                ·
                  refine ⟨22232604134322122212343557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29643472179096162949791409 22232604134322122212343557)
                  ·
                    refine ⟨4168613275185397914814417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22232604134322122212343557 4168613275185397914814417)
                    ·
                      refine ⟨3126459956389048436110813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4168613275185397914814417 3126459956389048436110813)
                      ·
                        rfl

theorem cell23_6088759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 2, 4, 2].length) (baseStart_6088759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088759 prefixEnd_6088759 := by exact prefixLift 6088759
  have htrace : WordTrace (prefixWord ++ tailWord_6088759) baseStart_6088759 baseEnd_6088759 := by
    simpa [prefixWord, tailWord_6088759, baseEnd_6088759] using wordTrace_append hprefix tailTrace_6088759
  have hstable : (prefixWord ++ tailWord_6088759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088759).length < 2 ^ (prefixWord ++ tailWord_6088759).sum := by decide
  have hdescent : baseEnd_6088759 < baseStart_6088759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088832 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 4]
def baseStart_6088832 : Nat := 118140960795 + 6088832 * 2 ^ 59
def prefixEnd_6088832 : Nat := 4983230072969 + 3 ^ 40 * 6088832 * 2
def baseEnd_6088832 : Nat := 3126497440476826650497977

theorem tailTrace_6088832 : CollatzResearch.WordTrace tailWord_6088832 prefixEnd_6088832 3126497440476826650497977 := by
  unfold tailWord_6088832
  simp only [CollatzResearch.WordTrace]
  refine ⟨111038973738604514280430375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148051964984806019040573833 111038973738604514280430375)
  ·
    refine ⟨166558460607906771420645563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111038973738604514280430375 166558460607906771420645563)
    ·
      refine ⟨249837690911860157130968345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166558460607906771420645563 249837690911860157130968345)
      ·
        refine ⟨187378268183895117848226259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249837690911860157130968345 187378268183895117848226259)
        ·
          refine ⟨281067402275842676772339389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187378268183895117848226259 281067402275842676772339389)
          ·
            refine ⟨105400275853441003789627271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 281067402275842676772339389 105400275853441003789627271)
            ·
              refine ⟨158100413780161505684440907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105400275853441003789627271 158100413780161505684440907)
              ·
                refine ⟨237150620670242258526661361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158100413780161505684440907 237150620670242258526661361)
                ·
                  refine ⟨177862965502681693894996021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 237150620670242258526661361 177862965502681693894996021)
                  ·
                    refine ⟨16674653015876408802655877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 177862965502681693894996021 16674653015876408802655877)
                    ·
                      refine ⟨3126497440476826650497977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16674653015876408802655877 3126497440476826650497977)
                      ·
                        rfl

theorem cell23_6088832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 4].length) (baseStart_6088832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088832 prefixEnd_6088832 := by exact prefixLift 6088832
  have htrace : WordTrace (prefixWord ++ tailWord_6088832) baseStart_6088832 baseEnd_6088832 := by
    simpa [prefixWord, tailWord_6088832, baseEnd_6088832] using wordTrace_append hprefix tailTrace_6088832
  have hstable : (prefixWord ++ tailWord_6088832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088832).length < 2 ^ (prefixWord ++ tailWord_6088832).sum := by decide
  have hdescent : baseEnd_6088832 < baseStart_6088832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088833 : List Nat := [1, 2, 4, 2, 3, 2, 2, 1, 6]
def baseStart_6088833 : Nat := 118140960795 + 6088833 * 2 ^ 59
def prefixEnd_6088833 : Nat := 4983230072969 + 3 ^ 40 * 6088833 * 2
def baseEnd_6088833 : Nat := 347388661550831238509497

theorem tailTrace_6088833 : CollatzResearch.WordTrace tailWord_6088833 prefixEnd_6088833 347388661550831238509497 := by
  unfold tailWord_6088833
  simp only [CollatzResearch.WordTrace]
  refine ⟨222077983950205405731647153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148051989300136937154431435 222077983950205405731647153)
  ·
    refine ⟨166558487962654054298735365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222077983950205405731647153 166558487962654054298735365)
    ·
      refine ⟨31229716492997635181012881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166558487962654054298735365 31229716492997635181012881)
      ·
        refine ⟨23422287369748226385759661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31229716492997635181012881 23422287369748226385759661)
        ·
          refine ⟨8783357763655584894659873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23422287369748226385759661 8783357763655584894659873)
          ·
            refine ⟨6587518322741688670994905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8783357763655584894659873 6587518322741688670994905)
            ·
              refine ⟨4940638742056266503246179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6587518322741688670994905 4940638742056266503246179)
              ·
                refine ⟨7410958113084399754869269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4940638742056266503246179 7410958113084399754869269)
                ·
                  refine ⟨347388661550831238509497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7410958113084399754869269 347388661550831238509497)
                  ·
                    rfl

theorem cell23_6088833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 2, 1, 6].length) (baseStart_6088833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088833 prefixEnd_6088833 := by exact prefixLift 6088833
  have htrace : WordTrace (prefixWord ++ tailWord_6088833) baseStart_6088833 baseEnd_6088833 := by
    simpa [prefixWord, tailWord_6088833, baseEnd_6088833] using wordTrace_append hprefix tailTrace_6088833
  have hstable : (prefixWord ++ tailWord_6088833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088833).length < 2 ^ (prefixWord ++ tailWord_6088833).sum := by decide
  have hdescent : baseEnd_6088833 < baseStart_6088833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088836 : List Nat := [2, 3, 2, 1, 2, 1, 1, 2, 4, 3, 2]
def baseStart_6088836 : Nat := 118140960795 + 6088836 * 2 ^ 59
def prefixEnd_6088836 : Nat := 4983230072969 + 3 ^ 40 * 6088836 * 2
def baseEnd_6088836 : Nat := 3126499494399444634847959

theorem tailTrace_6088836 : CollatzResearch.WordTrace tailWord_6088836 prefixEnd_6088836 3126499494399444634847959 := by
  unfold tailWord_6088836
  simp only [CollatzResearch.WordTrace]
  refine ⟨111039046684597268622003181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148052062246129691496004241 111039046684597268622003181)
  ·
    refine ⟨41639642506723975733251193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111039046684597268622003181 41639642506723975733251193)
    ·
      refine ⟨31229731880042981799938395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41639642506723975733251193 31229731880042981799938395)
      ·
        refine ⟨46844597820064472699907593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31229731880042981799938395 46844597820064472699907593)
        ·
          refine ⟨35133448365048354524930695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46844597820064472699907593 35133448365048354524930695)
          ·
            refine ⟨52700172547572531787396043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35133448365048354524930695 52700172547572531787396043)
            ·
              refine ⟨79050258821358797681094065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52700172547572531787396043 79050258821358797681094065)
              ·
                refine ⟨59287694116019098260820549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79050258821358797681094065 59287694116019098260820549)
                ·
                  refine ⟨11116442646753580923903853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59287694116019098260820549 11116442646753580923903853)
                  ·
                    refine ⟨4168665992532592846463945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11116442646753580923903853 4168665992532592846463945)
                    ·
                      refine ⟨3126499494399444634847959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4168665992532592846463945 3126499494399444634847959)
                      ·
                        rfl

theorem cell23_6088836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_6088836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088836 prefixEnd_6088836 := by exact prefixLift 6088836
  have htrace : WordTrace (prefixWord ++ tailWord_6088836) baseStart_6088836 baseEnd_6088836 := by
    simpa [prefixWord, tailWord_6088836, baseEnd_6088836] using wordTrace_append hprefix tailTrace_6088836
  have hstable : (prefixWord ++ tailWord_6088836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088836).length < 2 ^ (prefixWord ++ tailWord_6088836).sum := by decide
  have hdescent : baseEnd_6088836 < baseStart_6088836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088846 : List Nat := [4, 1, 1, 3, 3, 1, 1, 1, 3, 5]
def baseStart_6088846 : Nat := 118140960795 + 6088846 * 2 ^ 59
def prefixEnd_6088846 : Nat := 4983230072969 + 3 ^ 40 * 6088846 * 2
def baseEnd_6088846 : Nat := 1042168209735329865240971

theorem tailTrace_6088846 : CollatzResearch.WordTrace tailWord_6088846 prefixEnd_6088846 1042168209735329865240971 := by
  unfold tailWord_6088846
  simp only [CollatzResearch.WordTrace]
  refine ⟨27759807262394788618983799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148052305399438872634580261 27759807262394788618983799)
  ·
    refine ⟨41639710893592182928475699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27759807262394788618983799 41639710893592182928475699)
    ·
      refine ⟨62459566340388274392713549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41639710893592182928475699 62459566340388274392713549)
      ·
        refine ⟨23422337377645602897267581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62459566340388274392713549 23422337377645602897267581)
        ·
          refine ⟨8783376516617101086475343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23422337377645602897267581 8783376516617101086475343)
          ·
            refine ⟨13175064774925651629713015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8783376516617101086475343 13175064774925651629713015)
            ·
              refine ⟨19762597162388477444569523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13175064774925651629713015 19762597162388477444569523)
              ·
                refine ⟨29643895743582716166854285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19762597162388477444569523 29643895743582716166854285)
                ·
                  refine ⟨11116460903843518562570357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29643895743582716166854285 11116460903843518562570357)
                  ·
                    refine ⟨1042168209735329865240971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11116460903843518562570357 1042168209735329865240971)
                    ·
                      rfl

theorem cell23_6088846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 3, 5].length) (baseStart_6088846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088846 prefixEnd_6088846 := by exact prefixLift 6088846
  have htrace : WordTrace (prefixWord ++ tailWord_6088846) baseStart_6088846 baseEnd_6088846 := by
    simpa [prefixWord, tailWord_6088846, baseEnd_6088846] using wordTrace_append hprefix tailTrace_6088846
  have hstable : (prefixWord ++ tailWord_6088846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088846).length < 2 ^ (prefixWord ++ tailWord_6088846).sum := by decide
  have hdescent : baseEnd_6088846 < baseStart_6088846 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088863 : List Nat := [1, 1, 2, 6, 1, 2, 3, 1, 1, 5]
def baseStart_6088863 : Nat := 118140960795 + 6088863 * 2 ^ 59
def prefixEnd_6088863 : Nat := 4983230072969 + 3 ^ 40 * 6088863 * 2
def baseEnd_6088863 : Nat := 1042171119459038676403445

theorem tailTrace_6088863 : CollatzResearch.WordTrace tailWord_6088863 prefixEnd_6088863 1042171119459038676403445 := by
  unfold tailWord_6088863
  simp only [CollatzResearch.WordTrace]
  refine ⟨222079078140096720855239243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148052718760064480570159495 222079078140096720855239243)
  ·
    refine ⟨333118617210145081282858865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222079078140096720855239243 333118617210145081282858865)
    ·
      refine ⟨249838962907608810962144149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333118617210145081282858865 249838962907608810962144149)
      ·
        refine ⟨11711201386294163013850507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 249838962907608810962144149 11711201386294163013850507)
        ·
          refine ⟨17566802079441244520775761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11711201386294163013850507 17566802079441244520775761)
          ·
            refine ⟨13175101559580933390581821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17566802079441244520775761 13175101559580933390581821)
            ·
              refine ⟨4940663084842850021468183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13175101559580933390581821 4940663084842850021468183)
              ·
                refine ⟨7410994627264275032202275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4940663084842850021468183 7410994627264275032202275)
                ·
                  refine ⟨11116491940896412548303413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7410994627264275032202275 11116491940896412548303413)
                  ·
                    refine ⟨1042171119459038676403445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11116491940896412548303413 1042171119459038676403445)
                    ·
                      rfl

theorem cell23_6088863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 1, 5].length) (baseStart_6088863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088863 prefixEnd_6088863 := by exact prefixLift 6088863
  have htrace : WordTrace (prefixWord ++ tailWord_6088863) baseStart_6088863 baseEnd_6088863 := by
    simpa [prefixWord, tailWord_6088863, baseEnd_6088863] using wordTrace_append hprefix tailTrace_6088863
  have hstable : (prefixWord ++ tailWord_6088863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088863).length < 2 ^ (prefixWord ++ tailWord_6088863).sum := by decide
  have hdescent : baseEnd_6088863 < baseStart_6088863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088877 : List Nat := [1, 5, 2, 1, 2, 1, 4, 2, 1, 1, 3]
def baseStart_6088877 : Nat := 118140960795 + 6088877 * 2 ^ 59
def prefixEnd_6088877 : Nat := 4983230072969 + 3 ^ 40 * 6088877 * 2
def baseEnd_6088877 : Nat := 3126520547106278974435271

theorem tailTrace_6088877 : CollatzResearch.WordTrace tailWord_6088877 prefixEnd_6088877 3126520547106278974435271 := by
  unfold tailWord_6088877
  simp only [CollatzResearch.WordTrace]
  refine ⟨222079588762046001246248885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148053059174697334164165923 222079588762046001246248885)
  ·
    refine ⟨20819961446441812616835833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 222079588762046001246248885 20819961446441812616835833)
    ·
      refine ⟨15614971084831359462626875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20819961446441812616835833 15614971084831359462626875)
      ·
        refine ⟨23422456627247039193940313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15614971084831359462626875 23422456627247039193940313)
        ·
          refine ⟨17566842470435279395455235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23422456627247039193940313 17566842470435279395455235)
          ·
            refine ⟨26350263705652919093182853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17566842470435279395455235 26350263705652919093182853)
            ·
              refine ⟨4940674444809922329971785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26350263705652919093182853 4940674444809922329971785)
              ·
                refine ⟨3705505833607441747478839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4940674444809922329971785 3705505833607441747478839)
                ·
                  refine ⟨5558258750411162621218259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3705505833607441747478839 5558258750411162621218259)
                  ·
                    refine ⟨8337388125616743931827389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5558258750411162621218259 8337388125616743931827389)
                    ·
                      refine ⟨3126520547106278974435271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8337388125616743931827389 3126520547106278974435271)
                      ·
                        rfl

theorem cell23_6088877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_6088877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088877 prefixEnd_6088877 := by exact prefixLift 6088877
  have htrace : WordTrace (prefixWord ++ tailWord_6088877) baseStart_6088877 baseEnd_6088877 := by
    simpa [prefixWord, tailWord_6088877, baseEnd_6088877] using wordTrace_append hprefix tailTrace_6088877
  have hstable : (prefixWord ++ tailWord_6088877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088877).length < 2 ^ (prefixWord ++ tailWord_6088877).sum := by decide
  have hdescent : baseEnd_6088877 < baseStart_6088877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088896 : List Nat := [2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 4]
def baseStart_6088896 : Nat := 118140960795 + 6088896 * 2 ^ 59
def prefixEnd_6088896 : Nat := 4983230072969 + 3 ^ 40 * 6088896 * 2
def baseEnd_6088896 : Nat := 3126530303238714400097683

theorem tailTrace_6088896 : CollatzResearch.WordTrace tailWord_6088896 prefixEnd_6088896 3126530303238714400097683 := by
  unfold tailWord_6088896
  simp only [CollatzResearch.WordTrace]
  refine ⟨111040140874488583745595271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148053521165984778327460361 111040140874488583745595271)
  ·
    refine ⟨166560211311732875618392907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111040140874488583745595271 166560211311732875618392907)
    ·
      refine ⟨249840316967599313427589361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166560211311732875618392907 249840316967599313427589361)
      ·
        refine ⟨187380237725699485070692021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249840316967599313427589361 187380237725699485070692021)
        ·
          refine ⟨17566897286784326725377377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 187380237725699485070692021 17566897286784326725377377)
          ·
            refine ⟨13175172965088245044033033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17566897286784326725377377 13175172965088245044033033)
            ·
              refine ⟨9881379723816183783024775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13175172965088245044033033 9881379723816183783024775)
              ·
                refine ⟨14822069585724275674537163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9881379723816183783024775 14822069585724275674537163)
                ·
                  refine ⟨22233104378586413511805745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14822069585724275674537163 22233104378586413511805745)
                  ·
                    refine ⟨16674828283939810133854309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22233104378586413511805745 16674828283939810133854309)
                    ·
                      refine ⟨3126530303238714400097683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16674828283939810133854309 3126530303238714400097683)
                      ·
                        rfl

theorem cell23_6088896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 4].length) (baseStart_6088896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088896 prefixEnd_6088896 := by exact prefixLift 6088896
  have htrace : WordTrace (prefixWord ++ tailWord_6088896) baseStart_6088896 baseEnd_6088896 := by
    simpa [prefixWord, tailWord_6088896, baseEnd_6088896] using wordTrace_append hprefix tailTrace_6088896
  have hstable : (prefixWord ++ tailWord_6088896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088896).length < 2 ^ (prefixWord ++ tailWord_6088896).sum := by decide
  have hdescent : baseEnd_6088896 < baseStart_6088896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088900 : List Nat := [2, 3, 3, 1, 2, 2, 1, 2, 3, 2, 2]
def baseStart_6088900 : Nat := 118140960795 + 6088900 * 2 ^ 59
def prefixEnd_6088900 : Nat := 4983230072969 + 3 ^ 40 * 6088900 * 2
def baseEnd_6088900 : Nat := 3126532357161332384447665

theorem tailTrace_6088900 : CollatzResearch.WordTrace tailWord_6088900 prefixEnd_6088900 3126532357161332384447665 := by
  unfold tailWord_6088900
  simp only [CollatzResearch.WordTrace]
  refine ⟨111040213820481338087168077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148053618427308450782890769 111040213820481338087168077)
  ·
    refine ⟨41640080182680501782688029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111040213820481338087168077 41640080182680501782688029)
    ·
      refine ⟨15615030068505188168508011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41640080182680501782688029 15615030068505188168508011)
      ·
        refine ⟨23422545102757782252762017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15615030068505188168508011 23422545102757782252762017)
        ·
          refine ⟨17566908827068336689571513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23422545102757782252762017 17566908827068336689571513)
          ·
            refine ⟨13175181620301252517178635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17566908827068336689571513 13175181620301252517178635)
            ·
              refine ⟨19762772430451878775767953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13175181620301252517178635 19762772430451878775767953)
              ·
                refine ⟨14822079322838909081825965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19762772430451878775767953 14822079322838909081825965)
                ·
                  refine ⟨5558279746064590905684737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14822079322838909081825965 5558279746064590905684737)
                  ·
                    refine ⟨4168709809548443179263553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5558279746064590905684737 4168709809548443179263553)
                    ·
                      refine ⟨3126532357161332384447665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4168709809548443179263553 3126532357161332384447665)
                      ·
                        rfl

theorem cell23_6088900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_6088900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088900 prefixEnd_6088900 := by exact prefixLift 6088900
  have htrace : WordTrace (prefixWord ++ tailWord_6088900) baseStart_6088900 baseEnd_6088900 := by
    simpa [prefixWord, tailWord_6088900, baseEnd_6088900] using wordTrace_append hprefix tailTrace_6088900
  have hstable : (prefixWord ++ tailWord_6088900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088900).length < 2 ^ (prefixWord ++ tailWord_6088900).sum := by decide
  have hdescent : baseEnd_6088900 < baseStart_6088900 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088917 : List Nat := [1, 3, 2, 4, 3, 1, 2, 1, 1, 1, 4]
def baseStart_6088917 : Nat := 118140960795 + 6088917 * 2 ^ 59
def prefixEnd_6088917 : Nat := 4983230072969 + 3 ^ 40 * 6088917 * 2
def baseEnd_6088917 : Nat := 3126541086332458817935087

theorem tailTrace_6088917 : CollatzResearch.WordTrace tailWord_6088917 prefixEnd_6088917 3126541086332458817935087 := by
  unfold tailWord_6088917
  simp only [CollatzResearch.WordTrace]
  refine ⟨222081047681901088077705005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148054031787934058718470003 222081047681901088077705005)
  ·
    refine ⟨83280392880712908029139377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222081047681901088077705005 83280392880712908029139377)
    ·
      refine ⟨62460294660534681021854533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83280392880712908029139377 62460294660534681021854533)
      ·
        refine ⟨11711305248850252691597725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62460294660534681021854533 11711305248850252691597725)
        ·
          refine ⟨4391739468318844759349147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11711305248850252691597725 4391739468318844759349147)
          ·
            refine ⟨6587609202478267139023721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4391739468318844759349147 6587609202478267139023721)
            ·
              refine ⟨4940706901858700354267791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6587609202478267139023721 4940706901858700354267791)
              ·
                refine ⟨7411060352788050531401687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4940706901858700354267791 7411060352788050531401687)
                ·
                  refine ⟨11116590529182075797102531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7411060352788050531401687 11116590529182075797102531)
                  ·
                    refine ⟨16674885793773113695653797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11116590529182075797102531 16674885793773113695653797)
                    ·
                      refine ⟨3126541086332458817935087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16674885793773113695653797 3126541086332458817935087)
                      ·
                        rfl

theorem cell23_6088917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_6088917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088917 prefixEnd_6088917 := by exact prefixLift 6088917
  have htrace : WordTrace (prefixWord ++ tailWord_6088917) baseStart_6088917 baseEnd_6088917 := by
    simpa [prefixWord, tailWord_6088917, baseEnd_6088917] using wordTrace_append hprefix tailTrace_6088917
  have hstable : (prefixWord ++ tailWord_6088917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088917).length < 2 ^ (prefixWord ++ tailWord_6088917).sum := by decide
  have hdescent : baseEnd_6088917 < baseStart_6088917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088920 : List Nat := [2, 1, 2, 2, 4, 3, 2, 1, 1, 2, 3]
def baseStart_6088920 : Nat := 118140960795 + 6088920 * 2 ^ 59
def prefixEnd_6088920 : Nat := 4983230072969 + 3 ^ 40 * 6088920 * 2
def baseEnd_6088920 : Nat := 3126542626774422306197573

theorem tailTrace_6088920 : CollatzResearch.WordTrace tailWord_6088920 prefixEnd_6088920 3126542626774422306197573 := by
  unfold tailWord_6088920
  simp only [CollatzResearch.WordTrace]
  refine ⟨111040578550445109795032107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148054104733926813060042809 111040578550445109795032107)
  ·
    refine ⟨166560867825667664692548161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111040578550445109795032107 166560867825667664692548161)
    ·
      refine ⟨124920650869250748519411121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166560867825667664692548161 124920650869250748519411121)
      ·
        refine ⟨93690488151938061389558341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124920650869250748519411121 93690488151938061389558341)
        ·
          refine ⟨17566966528488386510542189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93690488151938061389558341 17566966528488386510542189)
          ·
            refine ⟨6587612448183144941453321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17566966528488386510542189 6587612448183144941453321)
            ·
              refine ⟨4940709336137358706089991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6587612448183144941453321 4940709336137358706089991)
              ·
                refine ⟨7411064004206038059134987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4940709336137358706089991 7411064004206038059134987)
                ·
                  refine ⟨11116596006309057088702481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7411064004206038059134987 11116596006309057088702481)
                  ·
                    refine ⟨8337447004731792816526861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11116596006309057088702481 8337447004731792816526861)
                    ·
                      refine ⟨3126542626774422306197573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8337447004731792816526861 3126542626774422306197573)
                      ·
                        rfl

theorem cell23_6088920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 1, 2, 3].length) (baseStart_6088920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088920 prefixEnd_6088920 := by exact prefixLift 6088920
  have htrace : WordTrace (prefixWord ++ tailWord_6088920) baseStart_6088920 baseEnd_6088920 := by
    simpa [prefixWord, tailWord_6088920, baseEnd_6088920] using wordTrace_append hprefix tailTrace_6088920
  have hstable : (prefixWord ++ tailWord_6088920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088920).length < 2 ^ (prefixWord ++ tailWord_6088920).sum := by decide
  have hdescent : baseEnd_6088920 < baseStart_6088920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088933 : List Nat := [1, 3, 1, 4, 2, 2, 1, 1, 4, 1, 3]
def baseStart_6088933 : Nat := 118140960795 + 6088933 * 2 ^ 59
def prefixEnd_6088933 : Nat := 4983230072969 + 3 ^ 40 * 6088933 * 2
def baseEnd_6088933 : Nat := 3126549302022930755335013

theorem tailTrace_6088933 : CollatzResearch.WordTrace tailWord_6088933 prefixEnd_6088933 3126549302022930755335013 := by
  unfold tailWord_6088933
  simp only [CollatzResearch.WordTrace]
  refine ⟨222081631249843122810287453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148054420833228748540191635 222081631249843122810287453)
  ·
    refine ⟨83280611718691171053857795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222081631249843122810287453 83280611718691171053857795)
    ·
      refine ⟨124920917578036756580786693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83280611718691171053857795 124920917578036756580786693)
      ·
        refine ⟨23422672045881891858897505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124920917578036756580786693 23422672045881891858897505)
        ·
          refine ⟨17567004034411418894173129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23422672045881891858897505 17567004034411418894173129)
          ·
            refine ⟨13175253025808564170629847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17567004034411418894173129 13175253025808564170629847)
            ·
              refine ⟨19762879538712846255944771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13175253025808564170629847 19762879538712846255944771)
              ·
                refine ⟨29644319308069269383917157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19762879538712846255944771 29644319308069269383917157)
                ·
                  refine ⟨5558309870262988009484467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29644319308069269383917157 5558309870262988009484467)
                  ·
                    refine ⟨8337464805394482014226701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5558309870262988009484467 8337464805394482014226701)
                    ·
                      refine ⟨3126549302022930755335013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8337464805394482014226701 3126549302022930755335013)
                      ·
                        rfl

theorem cell23_6088933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_6088933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088933 prefixEnd_6088933 := by exact prefixLift 6088933
  have htrace : WordTrace (prefixWord ++ tailWord_6088933) baseStart_6088933 baseEnd_6088933 := by
    simpa [prefixWord, tailWord_6088933, baseEnd_6088933] using wordTrace_append hprefix tailTrace_6088933
  have hstable : (prefixWord ++ tailWord_6088933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088933).length < 2 ^ (prefixWord ++ tailWord_6088933).sum := by decide
  have hdescent : baseEnd_6088933 < baseStart_6088933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088959 : List Nat := [1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 5]
def baseStart_6088959 : Nat := 118140960795 + 6088959 * 2 ^ 59
def prefixEnd_6088959 : Nat := 4983230072969 + 3 ^ 40 * 6088959 * 2
def baseEnd_6088959 : Nat := 3126562652519947653609893

theorem tailTrace_6088959 : CollatzResearch.WordTrace tailWord_6088959 prefixEnd_6088959 3126562652519947653609893 := by
  unfold tailWord_6088959
  simp only [CollatzResearch.WordTrace]
  refine ⟨222082579547748929250733931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148055053031832619500489287 222082579547748929250733931)
  ·
    refine ⟨333123869321623393876100897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222082579547748929250733931 333123869321623393876100897)
    ·
      refine ⟨249842901991217545407075673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333123869321623393876100897 249842901991217545407075673)
      ·
        refine ⟨187382176493413159055306755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249842901991217545407075673 187382176493413159055306755)
        ·
          refine ⟨281073264740119738582960133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187382176493413159055306755 281073264740119738582960133)
          ·
            refine ⟨52701237138772450984305025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 281073264740119738582960133 52701237138772450984305025)
            ·
              refine ⟨39525927854079338238228769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52701237138772450984305025 39525927854079338238228769)
              ·
                refine ⟨29644445890559503678671577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39525927854079338238228769 29644445890559503678671577)
                ·
                  refine ⟨22233334417919627759003683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29644445890559503678671577 22233334417919627759003683)
                  ·
                    refine ⟨33350001626879441638505525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22233334417919627759003683 33350001626879441638505525)
                    ·
                      refine ⟨3126562652519947653609893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33350001626879441638505525 3126562652519947653609893)
                      ·
                        rfl

theorem cell23_6088959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 1, 5].length) (baseStart_6088959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088959 prefixEnd_6088959 := by exact prefixLift 6088959
  have htrace : WordTrace (prefixWord ++ tailWord_6088959) baseStart_6088959 baseEnd_6088959 := by
    simpa [prefixWord, tailWord_6088959, baseEnd_6088959] using wordTrace_append hprefix tailTrace_6088959
  have hstable : (prefixWord ++ tailWord_6088959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088959).length < 2 ^ (prefixWord ++ tailWord_6088959).sum := by decide
  have hdescent : baseEnd_6088959 < baseStart_6088959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6088996 : List Nat := [2, 3, 1, 3, 1, 2, 3, 1, 7]
def baseStart_6088996 : Nat := 118140960795 + 6088996 * 2 ^ 59
def prefixEnd_6088996 : Nat := 4983230072969 + 3 ^ 40 * 6088996 * 2
def baseEnd_6088996 : Nat := 347397961256018223205247

theorem tailTrace_6088996 : CollatzResearch.WordTrace tailWord_6088996 prefixEnd_6088996 347397961256018223205247 := by
  unfold tailWord_6088996
  simp only [CollatzResearch.WordTrace]
  refine ⟨111041964524307442284915421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148055952699076589713220561 111041964524307442284915421)
  ·
    refine ⟨41640736696615290856843283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111041964524307442284915421 41640736696615290856843283)
    ·
      refine ⟨62461105044922936285264925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41640736696615290856843283 62461105044922936285264925)
      ·
        refine ⟨23422914391846101106974347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62461105044922936285264925 23422914391846101106974347)
        ·
          refine ⟨35134371587769151660461521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23422914391846101106974347 35134371587769151660461521)
          ·
            refine ⟨26350778690826863745346141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35134371587769151660461521 26350778690826863745346141)
            ·
              refine ⟨9881542009060073904504803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26350778690826863745346141 9881542009060073904504803)
              ·
                refine ⟨14822313013590110856757205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9881542009060073904504803 14822313013590110856757205)
                ·
                  refine ⟨347397961256018223205247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14822313013590110856757205 347397961256018223205247)
                  ·
                    rfl

theorem cell23_6088996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 7].length) (baseStart_6088996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6088996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6088996 prefixEnd_6088996 := by exact prefixLift 6088996
  have htrace : WordTrace (prefixWord ++ tailWord_6088996) baseStart_6088996 baseEnd_6088996 := by
    simpa [prefixWord, tailWord_6088996, baseEnd_6088996] using wordTrace_append hprefix tailTrace_6088996
  have hstable : (prefixWord ++ tailWord_6088996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6088996).length < 2 ^ (prefixWord ++ tailWord_6088996).sum := by decide
  have hdescent : baseEnd_6088996 < baseStart_6088996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6088996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089049 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 1, 5, 5]
def baseStart_6089049 : Nat := 118140960795 + 6089049 * 2 ^ 59
def prefixEnd_6089049 : Nat := 4983230072969 + 3 ^ 40 * 6089049 * 2
def baseEnd_6089049 : Nat := 3126608865778852301484479

theorem tailTrace_6089049 : CollatzResearch.WordTrace tailWord_6089049 prefixEnd_6089049 3126608865778852301484479 := by
  unfold tailWord_6089049
  simp only [CollatzResearch.WordTrace]
  refine ⟨222085862117422874621510201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148057241411615249747673467 222085862117422874621510201)
  ·
    refine ⟨166564396588067155966132651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222085862117422874621510201 166564396588067155966132651)
    ·
      refine ⟨249846594882100733949198977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166564396588067155966132651 249846594882100733949198977)
      ·
        refine ⟨187384946161575550461899233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249846594882100733949198977 187384946161575550461899233)
        ·
          refine ⟨140538709621181662846424425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187384946161575550461899233 140538709621181662846424425)
          ·
            refine ⟨105404032215886247134818319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140538709621181662846424425 105404032215886247134818319)
            ·
              refine ⟨158106048323829370702227479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105404032215886247134818319 158106048323829370702227479)
              ·
                refine ⟨237159072485744056053341219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158106048323829370702227479 237159072485744056053341219)
                ·
                  refine ⟨355738608728616084080011829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 237159072485744056053341219 355738608728616084080011829)
                  ·
                    refine ⟨33350494568307757882501109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 355738608728616084080011829 33350494568307757882501109)
                    ·
                      refine ⟨3126608865778852301484479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33350494568307757882501109 3126608865778852301484479)
                      ·
                        rfl

theorem cell23_6089049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_6089049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089049 prefixEnd_6089049 := by exact prefixLift 6089049
  have htrace : WordTrace (prefixWord ++ tailWord_6089049) baseStart_6089049 baseEnd_6089049 := by
    simpa [prefixWord, tailWord_6089049, baseEnd_6089049] using wordTrace_append hprefix tailTrace_6089049
  have hstable : (prefixWord ++ tailWord_6089049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089049).length < 2 ^ (prefixWord ++ tailWord_6089049).sum := by decide
  have hdescent : baseEnd_6089049 < baseStart_6089049 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089054 : List Nat := [4, 4, 2, 1, 1, 1, 1, 1, 2, 2, 4]
def baseStart_6089054 : Nat := 118140960795 + 6089054 * 2 ^ 59
def prefixEnd_6089054 : Nat := 4983230072969 + 3 ^ 40 * 6089054 * 2
def baseEnd_6089054 : Nat := 3126611433182124781921957

theorem tailTrace_6089054 : CollatzResearch.WordTrace tailWord_6089054 prefixEnd_6089054 3126611433182124781921957 := by
  unfold tailWord_6089054
  simp only [CollatzResearch.WordTrace]
  refine ⟨27760755560300595059430277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148057362988269840316961477 27760755560300595059430277)
  ·
    refine ⟨5205141667556361573643177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27760755560300595059430277 5205141667556361573643177)
    ·
      refine ⟨3903856250667271180232383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5205141667556361573643177 3903856250667271180232383)
      ·
        refine ⟨5855784376000906770348575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3903856250667271180232383 5855784376000906770348575)
        ·
          refine ⟨8783676564001360155522863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5855784376000906770348575 8783676564001360155522863)
          ·
            refine ⟨13175514846002040233284295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8783676564001360155522863 13175514846002040233284295)
            ·
              refine ⟨19763272269003060349926443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13175514846002040233284295 19763272269003060349926443)
              ·
                refine ⟨29644908403504590524889665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19763272269003060349926443 29644908403504590524889665)
                ·
                  refine ⟨22233681302628442893667249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29644908403504590524889665 22233681302628442893667249)
                  ·
                    refine ⟨16675260976971332170250437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22233681302628442893667249 16675260976971332170250437)
                    ·
                      refine ⟨3126611433182124781921957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16675260976971332170250437 3126611433182124781921957)
                      ·
                        rfl

theorem cell23_6089054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_6089054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089054 prefixEnd_6089054 := by exact prefixLift 6089054
  have htrace : WordTrace (prefixWord ++ tailWord_6089054) baseStart_6089054 baseEnd_6089054 := by
    simpa [prefixWord, tailWord_6089054, baseEnd_6089054] using wordTrace_append hprefix tailTrace_6089054
  have hstable : (prefixWord ++ tailWord_6089054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089054).length < 2 ^ (prefixWord ++ tailWord_6089054).sum := by decide
  have hdescent : baseEnd_6089054 < baseStart_6089054 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089063 : List Nat := [1, 1, 5, 1, 3, 1, 1, 1, 1, 6, 2]
def baseStart_6089063 : Nat := 118140960795 + 6089063 * 2 ^ 59
def prefixEnd_6089063 : Nat := 4983230072969 + 3 ^ 40 * 6089063 * 2
def baseEnd_6089063 : Nat := 3126616054508015246709415

theorem tailTrace_6089063 : CollatzResearch.WordTrace tailWord_6089063 prefixEnd_6089063 3126616054508015246709415 := by
  unfold tailWord_6089063
  simp only [CollatzResearch.WordTrace]
  refine ⟨222086372739372155012519843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148057581826248103341679895 222086372739372155012519843)
  ·
    refine ⟨333129559109058232518779765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222086372739372155012519843 333129559109058232518779765)
    ·
      refine ⟨31230896166474209298635603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 333129559109058232518779765 31230896166474209298635603)
      ·
        refine ⟨46846344249711313947953405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31230896166474209298635603 46846344249711313947953405)
        ·
          refine ⟨17567379093641742730482527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46846344249711313947953405 17567379093641742730482527)
          ·
            refine ⟨26351068640462614095723791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17567379093641742730482527 26351068640462614095723791)
            ·
              refine ⟨39526602960693921143585687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26351068640462614095723791 39526602960693921143585687)
              ·
                refine ⟨59289904441040881715378531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39526602960693921143585687 59289904441040881715378531)
                ·
                  refine ⟨88934856661561322573067797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59289904441040881715378531 88934856661561322573067797)
                  ·
                    refine ⟨4168821406010686995612553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 88934856661561322573067797 4168821406010686995612553)
                    ·
                      refine ⟨3126616054508015246709415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4168821406010686995612553 3126616054508015246709415)
                      ·
                        rfl

theorem cell23_6089063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_6089063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089063 prefixEnd_6089063 := by exact prefixLift 6089063
  have htrace : WordTrace (prefixWord ++ tailWord_6089063) baseStart_6089063 baseEnd_6089063 := by
    simpa [prefixWord, tailWord_6089063, baseEnd_6089063] using wordTrace_append hprefix tailTrace_6089063
  have hstable : (prefixWord ++ tailWord_6089063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089063).length < 2 ^ (prefixWord ++ tailWord_6089063).sum := by decide
  have hdescent : baseEnd_6089063 < baseStart_6089063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089083 : List Nat := [1, 1, 1, 1, 1, 7, 3, 1, 2, 2, 3]
def baseStart_6089083 : Nat := 118140960795 + 6089083 * 2 ^ 59
def prefixEnd_6089083 : Nat := 4983230072969 + 3 ^ 40 * 6089083 * 2
def baseEnd_6089083 : Nat := 3126626324121105168459323

theorem tailTrace_6089083 : CollatzResearch.WordTrace tailWord_6089083 prefixEnd_6089083 3126626324121105168459323 := by
  unfold tailWord_6089083
  simp only [CollatzResearch.WordTrace]
  refine ⟨222087102199299698428247903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148058068132866465618831935 222087102199299698428247903)
  ·
    refine ⟨333130653298949547642371855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222087102199299698428247903 333130653298949547642371855)
    ·
      refine ⟨499695979948424321463557783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333130653298949547642371855 499695979948424321463557783)
      ·
        refine ⟨749543969922636482195336675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 499695979948424321463557783 749543969922636482195336675)
        ·
          refine ⟨1124315954883954723293005013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 749543969922636482195336675 1124315954883954723293005013)
          ·
            refine ⟨26351155192592688827179805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1124315954883954723293005013 26351155192592688827179805)
            ·
              refine ⟨9881683197222258310192427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26351155192592688827179805 9881683197222258310192427)
              ·
                refine ⟨14822524795833387465288641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9881683197222258310192427 14822524795833387465288641)
                ·
                  refine ⟨11116893596875040598966481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14822524795833387465288641 11116893596875040598966481)
                  ·
                    refine ⟨8337670197656280449224861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11116893596875040598966481 8337670197656280449224861)
                    ·
                      refine ⟨3126626324121105168459323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8337670197656280449224861 3126626324121105168459323)
                      ·
                        rfl

theorem cell23_6089083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 2, 2, 3].length) (baseStart_6089083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089083 prefixEnd_6089083 := by exact prefixLift 6089083
  have htrace : WordTrace (prefixWord ++ tailWord_6089083) baseStart_6089083 baseEnd_6089083 := by
    simpa [prefixWord, tailWord_6089083, baseEnd_6089083] using wordTrace_append hprefix tailTrace_6089083
  have hstable : (prefixWord ++ tailWord_6089083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089083).length < 2 ^ (prefixWord ++ tailWord_6089083).sum := by decide
  have hdescent : baseEnd_6089083 < baseStart_6089083 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089123 : List Nat := [1, 1, 1, 4, 1, 4, 1, 2, 1, 5, 2]
def baseStart_6089123 : Nat := 118140960795 + 6089123 * 2 ^ 59
def prefixEnd_6089123 : Nat := 4983230072969 + 3 ^ 40 * 6089123 * 2
def baseEnd_6089123 : Nat := 3126646863347285011959139

theorem tailTrace_6089123 : CollatzResearch.WordTrace tailWord_6089123 prefixEnd_6089123 3126646863347285011959139 := by
  unfold tailWord_6089123
  simp only [CollatzResearch.WordTrace]
  refine ⟨222088561119154785259704023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148059040746103190173136015 222088561119154785259704023)
  ·
    refine ⟨333132841678732177889556035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222088561119154785259704023 333132841678732177889556035)
    ·
      refine ⟨499699262518098266834334053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333132841678732177889556035 499699262518098266834334053)
      ·
        refine ⟨93693611722143425031437635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 499699262518098266834334053 93693611722143425031437635)
        ·
          refine ⟨140540417583215137547156453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93693611722143425031437635 140540417583215137547156453)
          ·
            refine ⟨26351328296852838290091835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140540417583215137547156453 26351328296852838290091835)
            ·
              refine ⟨39526992445279257435137753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26351328296852838290091835 39526992445279257435137753)
              ·
                refine ⟨29645244333959443076353315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39526992445279257435137753 29645244333959443076353315)
                ·
                  refine ⟨44467866500939164614529973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29645244333959443076353315 44467866500939164614529973)
                  ·
                    refine ⟨4168862484463046682612185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44467866500939164614529973 4168862484463046682612185)
                    ·
                      refine ⟨3126646863347285011959139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4168862484463046682612185 3126646863347285011959139)
                      ·
                        rfl

theorem cell23_6089123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 5, 2].length) (baseStart_6089123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089123 prefixEnd_6089123 := by exact prefixLift 6089123
  have htrace : WordTrace (prefixWord ++ tailWord_6089123) baseStart_6089123 baseEnd_6089123 := by
    simpa [prefixWord, tailWord_6089123, baseEnd_6089123] using wordTrace_append hprefix tailTrace_6089123
  have hstable : (prefixWord ++ tailWord_6089123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089123).length < 2 ^ (prefixWord ++ tailWord_6089123).sum := by decide
  have hdescent : baseEnd_6089123 < baseStart_6089123 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089136 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 4]
def baseStart_6089136 : Nat := 118140960795 + 6089136 * 2 ^ 59
def prefixEnd_6089136 : Nat := 4983230072969 + 3 ^ 40 * 6089136 * 2
def baseEnd_6089136 : Nat := 3126653538595793461096579

theorem tailTrace_6089136 : CollatzResearch.WordTrace tailWord_6089136 prefixEnd_6089136 3126653538595793461096579 := by
  unfold tailWord_6089136
  simp only [CollatzResearch.WordTrace]
  refine ⟨111044517634053844239963631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148059356845405125653284841 111044517634053844239963631)
  ·
    refine ⟨166566776451080766359945447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111044517634053844239963631 166566776451080766359945447)
    ·
      refine ⟨249850164676621149539918171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166566776451080766359945447 249850164676621149539918171)
      ·
        refine ⟨374775247014931724309877257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249850164676621149539918171 374775247014931724309877257)
        ·
          refine ⟨281081435261198793232407943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374775247014931724309877257 281081435261198793232407943)
          ·
            refine ⟨421622152891798189848611915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281081435261198793232407943 421622152891798189848611915)
            ·
              refine ⟨632433229337697284772917873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 421622152891798189848611915 632433229337697284772917873)
              ·
                refine ⟨474324922003272963579688405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 632433229337697284772917873 474324922003272963579688405)
                ·
                  refine ⟨11116990359451710083898947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 474324922003272963579688405 11116990359451710083898947)
                  ·
                    refine ⟨16675485539177565125848421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11116990359451710083898947 16675485539177565125848421)
                    ·
                      refine ⟨3126653538595793461096579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16675485539177565125848421 3126653538595793461096579)
                      ·
                        rfl

theorem cell23_6089136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 4].length) (baseStart_6089136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089136 prefixEnd_6089136 := by exact prefixLift 6089136
  have htrace : WordTrace (prefixWord ++ tailWord_6089136) baseStart_6089136 baseEnd_6089136 := by
    simpa [prefixWord, tailWord_6089136, baseEnd_6089136] using wordTrace_append hprefix tailTrace_6089136
  have hstable : (prefixWord ++ tailWord_6089136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089136).length < 2 ^ (prefixWord ++ tailWord_6089136).sum := by decide
  have hdescent : baseEnd_6089136 < baseStart_6089136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089146 : List Nat := [3, 1, 1, 1, 2, 1, 1, 6, 1, 6]
def baseStart_6089146 : Nat := 118140960795 + 6089146 * 2 ^ 59
def prefixEnd_6089146 : Nat := 4983230072969 + 3 ^ 40 * 6089146 * 2
def baseEnd_6089146 : Nat := 1042219557800779473990511

theorem tailTrace_6089146 : CollatzResearch.WordTrace tailWord_6089146 prefixEnd_6089146 1042219557800779473990511 := by
  unfold tailWord_6089146
  simp only [CollatzResearch.WordTrace]
  refine ⟨55522349999517865046947823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148059599998714306791860861 55522349999517865046947823)
  ·
    refine ⟨83283524999276797570421735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55522349999517865046947823 83283524999276797570421735)
    ·
      refine ⟨124925287498915196355632603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83283524999276797570421735 124925287498915196355632603)
      ·
        refine ⟨187387931248372794533448905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124925287498915196355632603 187387931248372794533448905)
        ·
          refine ⟨140540948436279595900086679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187387931248372794533448905 140540948436279595900086679)
          ·
            refine ⟨210811422654419393850130019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140540948436279595900086679 210811422654419393850130019)
            ·
              refine ⟨316217133981629090775195029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210811422654419393850130019 316217133981629090775195029)
              ·
                refine ⟨14822678155388863630087267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 316217133981629090775195029 14822678155388863630087267)
                ·
                  refine ⟨22234017233083295445130901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14822678155388863630087267 22234017233083295445130901)
                  ·
                    refine ⟨1042219557800779473990511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22234017233083295445130901 1042219557800779473990511)
                    ·
                      rfl

theorem cell23_6089146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 1, 6].length) (baseStart_6089146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089146 prefixEnd_6089146 := by exact prefixLift 6089146
  have htrace : WordTrace (prefixWord ++ tailWord_6089146) baseStart_6089146 baseEnd_6089146 := by
    simpa [prefixWord, tailWord_6089146, baseEnd_6089146] using wordTrace_append hprefix tailTrace_6089146
  have hstable : (prefixWord ++ tailWord_6089146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089146).length < 2 ^ (prefixWord ++ tailWord_6089146).sum := by decide
  have hdescent : baseEnd_6089146 < baseStart_6089146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089163 : List Nat := [1, 1, 1, 1, 3, 3, 1, 6, 2, 4]
def baseStart_6089163 : Nat := 118140960795 + 6089163 * 2 ^ 59
def prefixEnd_6089163 : Nat := 4983230072969 + 3 ^ 40 * 6089163 * 2
def baseEnd_6089163 : Nat := 1042222467524488285152985

theorem tailTrace_6089163 : CollatzResearch.WordTrace tailWord_6089163 prefixEnd_6089163 1042222467524488285152985 := by
  unfold tailWord_6089163
  simp only [CollatzResearch.WordTrace]
  refine ⟨222090020039009872091160143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148060013359339914727440095 222090020039009872091160143)
  ·
    refine ⟨333135030058514808136740215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222090020039009872091160143 333135030058514808136740215)
    ·
      refine ⟨499702545087772212205110323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333135030058514808136740215 499702545087772212205110323)
      ·
        refine ⟨749553817631658318307665485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 499702545087772212205110323 749553817631658318307665485)
        ·
          refine ⟨281082681611871869365374557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 749553817631658318307665485 281082681611871869365374557)
          ·
            refine ⟨105406005604451951012015459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 281082681611871869365374557 105406005604451951012015459)
            ·
              refine ⟨158109008406677926518023189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105406005604451951012015459 158109008406677926518023189)
              ·
                refine ⟨7411359769063027805532337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 158109008406677926518023189 7411359769063027805532337)
                ·
                  refine ⟨5558519826797270854149253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7411359769063027805532337 5558519826797270854149253)
                  ·
                    refine ⟨1042222467524488285152985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5558519826797270854149253 1042222467524488285152985)
                    ·
                      rfl

theorem cell23_6089163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 2, 4].length) (baseStart_6089163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089163 prefixEnd_6089163 := by exact prefixLift 6089163
  have htrace : WordTrace (prefixWord ++ tailWord_6089163) baseStart_6089163 baseEnd_6089163 := by
    simpa [prefixWord, tailWord_6089163, baseEnd_6089163] using wordTrace_append hprefix tailTrace_6089163
  have hstable : (prefixWord ++ tailWord_6089163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089163).length < 2 ^ (prefixWord ++ tailWord_6089163).sum := by decide
  have hdescent : baseEnd_6089163 < baseStart_6089163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089164 : List Nat := [2, 2, 1, 4, 4, 1, 1, 1, 3, 1, 3]
def baseStart_6089164 : Nat := 118140960795 + 6089164 * 2 ^ 59
def prefixEnd_6089164 : Nat := 4983230072969 + 3 ^ 40 * 6089164 * 2
def baseEnd_6089164 : Nat := 3126667916054119351546451

theorem tailTrace_6089164 : CollatzResearch.WordTrace tailWord_6089164 prefixEnd_6089164 3126667916054119351546451 := by
  unfold tailWord_6089164
  simp only [CollatzResearch.WordTrace]
  refine ⟨111045028256003124630973273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148060037674670832841297697 111045028256003124630973273)
  ·
    refine ⟨83283771192002343473229955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111045028256003124630973273 83283771192002343473229955)
    ·
      refine ⟨124925656788003515209844933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83283771192002343473229955 124925656788003515209844933)
      ·
        refine ⟨23423560647750659101845925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124925656788003515209844933 23423560647750659101845925)
        ·
          refine ⟨4391917621453248581596111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23423560647750659101845925 4391917621453248581596111)
          ·
            refine ⟨6587876432179872872394167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4391917621453248581596111 6587876432179872872394167)
            ·
              refine ⟨9881814648269809308591251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6587876432179872872394167 9881814648269809308591251)
              ·
                refine ⟨14822721972404713962886877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9881814648269809308591251 14822721972404713962886877)
                ·
                  refine ⟨5558520739651767736082579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14822721972404713962886877 5558520739651767736082579)
                  ·
                    refine ⟨8337781109477651604123869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5558520739651767736082579 8337781109477651604123869)
                    ·
                      refine ⟨3126667916054119351546451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8337781109477651604123869 3126667916054119351546451)
                      ·
                        rfl

theorem cell23_6089164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_6089164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089164 prefixEnd_6089164 := by exact prefixLift 6089164
  have htrace : WordTrace (prefixWord ++ tailWord_6089164) baseStart_6089164 baseEnd_6089164 := by
    simpa [prefixWord, tailWord_6089164, baseEnd_6089164] using wordTrace_append hprefix tailTrace_6089164
  have hstable : (prefixWord ++ tailWord_6089164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089164).length < 2 ^ (prefixWord ++ tailWord_6089164).sum := by decide
  have hdescent : baseEnd_6089164 < baseStart_6089164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089173 : List Nat := [1, 3, 2, 3, 1, 2, 2, 2, 1, 1, 5]
def baseStart_6089173 : Nat := 118140960795 + 6089173 * 2 ^ 59
def prefixEnd_6089173 : Nat := 4983230072969 + 3 ^ 40 * 6089173 * 2
def baseEnd_6089173 : Nat := 3126672537380009816333909

theorem tailTrace_6089173 : CollatzResearch.WordTrace tailWord_6089173 prefixEnd_6089173 3126672537380009816333909 := by
  unfold tailWord_6089173
  simp only [CollatzResearch.WordTrace]
  refine ⟨222090384768973643799024173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148060256512649095866016115 222090384768973643799024173)
  ·
    refine ⟨83283894288365116424634065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222090384768973643799024173 83283894288365116424634065)
    ·
      refine ⟨62462920716273837318475549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83283894288365116424634065 62462920716273837318475549)
      ·
        refine ⟨23423595268602688994428331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62462920716273837318475549 23423595268602688994428331)
        ·
          refine ⟨35135392902904033491642497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23423595268602688994428331 35135392902904033491642497)
          ·
            refine ⟨26351544677178025118731873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35135392902904033491642497 26351544677178025118731873)
            ·
              refine ⟨19763658507883518839048905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26351544677178025118731873 19763658507883518839048905)
              ·
                refine ⟨14822743880912639129286679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19763658507883518839048905 14822743880912639129286679)
                ·
                  refine ⟨22234115821368958693930019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14822743880912639129286679 22234115821368958693930019)
                  ·
                    refine ⟨33351173732053438040895029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22234115821368958693930019 33351173732053438040895029)
                    ·
                      refine ⟨3126672537380009816333909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33351173732053438040895029 3126672537380009816333909)
                      ·
                        rfl

theorem cell23_6089173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_6089173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089173 prefixEnd_6089173 := by exact prefixLift 6089173
  have htrace : WordTrace (prefixWord ++ tailWord_6089173) baseStart_6089173 baseEnd_6089173 := by
    simpa [prefixWord, tailWord_6089173, baseEnd_6089173] using wordTrace_append hprefix tailTrace_6089173
  have hstable : (prefixWord ++ tailWord_6089173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089173).length < 2 ^ (prefixWord ++ tailWord_6089173).sum := by decide
  have hdescent : baseEnd_6089173 < baseStart_6089173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089187 : List Nat := [1, 1, 1, 6, 3, 2, 1, 2, 1, 1, 4]
def baseStart_6089187 : Nat := 118140960795 + 6089187 * 2 ^ 59
def prefixEnd_6089187 : Nat := 4983230072969 + 3 ^ 40 * 6089187 * 2
def baseEnd_6089187 : Nat := 3126679726109172761558845

theorem tailTrace_6089187 : CollatzResearch.WordTrace tailWord_6089187 prefixEnd_6089187 3126679726109172761558845 := by
  unfold tailWord_6089187
  simp only [CollatzResearch.WordTrace]
  refine ⟨222090895390922924190033815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148060596927281949460022543 222090895390922924190033815)
  ·
    refine ⟨333136343086384386285050723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222090895390922924190033815 333136343086384386285050723)
    ·
      refine ⟨499704514629576579427576085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333136343086384386285050723 499704514629576579427576085)
      ·
        refine ⟨23423649123261402160667629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 499704514629576579427576085 23423649123261402160667629)
        ·
          refine ⟨8783868421223025810250361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23423649123261402160667629 8783868421223025810250361)
          ·
            refine ⟨6587901315917269357687771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8783868421223025810250361 6587901315917269357687771)
            ·
              refine ⟨9881851973875904036531657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6587901315917269357687771 9881851973875904036531657)
              ·
                refine ⟨7411388980406928027398743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9881851973875904036531657 7411388980406928027398743)
                ·
                  refine ⟨11117083470610392041098115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7411388980406928027398743 11117083470610392041098115)
                  ·
                    refine ⟨16675625205915588061647173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11117083470610392041098115 16675625205915588061647173)
                    ·
                      refine ⟨3126679726109172761558845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16675625205915588061647173 3126679726109172761558845)
                      ·
                        rfl

theorem cell23_6089187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_6089187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089187 prefixEnd_6089187 := by exact prefixLift 6089187
  have htrace : WordTrace (prefixWord ++ tailWord_6089187) baseStart_6089187 baseEnd_6089187 := by
    simpa [prefixWord, tailWord_6089187, baseEnd_6089187] using wordTrace_append hprefix tailTrace_6089187
  have hstable : (prefixWord ++ tailWord_6089187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089187).length < 2 ^ (prefixWord ++ tailWord_6089187).sum := by decide
  have hdescent : baseEnd_6089187 < baseStart_6089187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089203 : List Nat := [1, 1, 1, 2, 2, 2, 5, 2, 1, 3, 3]
def baseStart_6089203 : Nat := 118140960795 + 6089203 * 2 ^ 59
def prefixEnd_6089203 : Nat := 4983230072969 + 3 ^ 40 * 6089203 * 2
def baseEnd_6089203 : Nat := 3126687941799644698958771

theorem tailTrace_6089203 : CollatzResearch.WordTrace tailWord_6089203 prefixEnd_6089203 3126687941799644698958771 := by
  unfold tailWord_6089203
  simp only [CollatzResearch.WordTrace]
  refine ⟨222091478958864958922616263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148060985972576639281744175 222091478958864958922616263)
  ·
    refine ⟨333137218438297438383924395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222091478958864958922616263 333137218438297438383924395)
    ·
      refine ⟨499705827657446157575886593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333137218438297438383924395 499705827657446157575886593)
      ·
        refine ⟨374779370743084618181914945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 499705827657446157575886593 374779370743084618181914945)
        ·
          refine ⟨281084528057313463636436209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374779370743084618181914945 281084528057313463636436209)
          ·
            refine ⟨210813396042985097727327157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281084528057313463636436209 210813396042985097727327157)
            ·
              refine ⟨19763755879029852911936921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 210813396042985097727327157 19763755879029852911936921)
              ·
                refine ⟨14822816909272389683952691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19763755879029852911936921 14822816909272389683952691)
                ·
                  refine ⟨22234225363908584525929037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14822816909272389683952691 22234225363908584525929037)
                  ·
                    refine ⟨8337834511465719197223389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22234225363908584525929037 8337834511465719197223389)
                    ·
                      refine ⟨3126687941799644698958771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8337834511465719197223389 3126687941799644698958771)
                      ·
                        rfl

theorem cell23_6089203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 2, 1, 3, 3].length) (baseStart_6089203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089203 prefixEnd_6089203 := by exact prefixLift 6089203
  have htrace : WordTrace (prefixWord ++ tailWord_6089203) baseStart_6089203 baseEnd_6089203 := by
    simpa [prefixWord, tailWord_6089203, baseEnd_6089203] using wordTrace_append hprefix tailTrace_6089203
  have hstable : (prefixWord ++ tailWord_6089203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089203).length < 2 ^ (prefixWord ++ tailWord_6089203).sum := by decide
  have hdescent : baseEnd_6089203 < baseStart_6089203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089270 : List Nat := [5, 1, 2, 1, 2, 1, 1, 2, 2, 6]
def baseStart_6089270 : Nat := 118140960795 + 6089270 * 2 ^ 59
def prefixEnd_6089270 : Nat := 4983230072969 + 3 ^ 40 * 6089270 * 2
def baseEnd_6089270 : Nat := 1042240781667831978940321

theorem tailTrace_6089270 : CollatzResearch.WordTrace tailWord_6089270 prefixEnd_6089270 1042240781667831978940321 := by
  unfold tailWord_6089270
  simp only [CollatzResearch.WordTrace]
  refine ⟨13880870165601389335331579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148062615099748152910203509 13880870165601389335331579)
  ·
    refine ⟨20821305248402084002997369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13880870165601389335331579 20821305248402084002997369)
    ·
      refine ⟨15615978936301563002248027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20821305248402084002997369 15615978936301563002248027)
      ·
        refine ⟨23423968404452344503372041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15615978936301563002248027 23423968404452344503372041)
        ·
          refine ⟨17567976303339258377529031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23423968404452344503372041 17567976303339258377529031)
          ·
            refine ⟨26351964455008887566293547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17567976303339258377529031 26351964455008887566293547)
            ·
              refine ⟨39527946682513331349440321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26351964455008887566293547 39527946682513331349440321)
              ·
                refine ⟨29645960011884998512080241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39527946682513331349440321 29645960011884998512080241)
                ·
                  refine ⟨22234470008913748884060181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29645960011884998512080241 22234470008913748884060181)
                  ·
                    refine ⟨1042240781667831978940321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22234470008913748884060181 1042240781667831978940321)
                    ·
                      rfl

theorem cell23_6089270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_6089270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089270 prefixEnd_6089270 := by exact prefixLift 6089270
  have htrace : WordTrace (prefixWord ++ tailWord_6089270) baseStart_6089270 baseEnd_6089270 := by
    simpa [prefixWord, tailWord_6089270, baseEnd_6089270] using wordTrace_append hprefix tailTrace_6089270
  have hstable : (prefixWord ++ tailWord_6089270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089270).length < 2 ^ (prefixWord ++ tailWord_6089270).sum := by decide
  have hdescent : baseEnd_6089270 < baseStart_6089270 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089273 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 4, 2, 4]
def baseStart_6089273 : Nat := 118140960795 + 6089273 * 2 ^ 59
def prefixEnd_6089273 : Nat := 4983230072969 + 3 ^ 40 * 6089273 * 2
def baseEnd_6089273 : Nat := 3126723885445459425083449

theorem tailTrace_6089273 : CollatzResearch.WordTrace tailWord_6089273 prefixEnd_6089273 3126723885445459425083449 := by
  unfold tailWord_6089273
  simp only [CollatzResearch.WordTrace]
  refine ⟨222094032068611360877664473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148062688045740907251776315 222094032068611360877664473)
  ·
    refine ⟨166570524051458520658248355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222094032068611360877664473 166570524051458520658248355)
    ·
      refine ⟨249855786077187780987372533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166570524051458520658248355 249855786077187780987372533)
      ·
        refine ⟨23423979944736354467566175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 249855786077187780987372533 23423979944736354467566175)
        ·
          refine ⟨35135969917104531701349263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23423979944736354467566175 35135969917104531701349263)
          ·
            refine ⟨52703954875656797552023895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35135969917104531701349263 52703954875656797552023895)
            ·
              refine ⟨79055932313485196328035843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52703954875656797552023895 79055932313485196328035843)
              ·
                refine ⟨118583898470227794492053765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79055932313485196328035843 118583898470227794492053765)
                ·
                  refine ⟨22234480963167711467260081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 118583898470227794492053765 22234480963167711467260081)
                  ·
                    refine ⟨16675860722375783600445061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22234480963167711467260081 16675860722375783600445061)
                    ·
                      refine ⟨3126723885445459425083449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16675860722375783600445061 3126723885445459425083449)
                      ·
                        rfl

theorem cell23_6089273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_6089273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089273 prefixEnd_6089273 := by exact prefixLift 6089273
  have htrace : WordTrace (prefixWord ++ tailWord_6089273) baseStart_6089273 baseEnd_6089273 := by
    simpa [prefixWord, tailWord_6089273, baseEnd_6089273] using wordTrace_append hprefix tailTrace_6089273
  have hstable : (prefixWord ++ tailWord_6089273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089273).length < 2 ^ (prefixWord ++ tailWord_6089273).sum := by decide
  have hdescent : baseEnd_6089273 < baseStart_6089273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089313 : List Nat := [1, 2, 3, 1, 1, 4, 2, 1, 1, 7]
def baseStart_6089313 : Nat := 118140960795 + 6089313 * 2 ^ 59
def prefixEnd_6089313 : Nat := 4983230072969 + 3 ^ 40 * 6089313 * 2
def baseEnd_6089313 : Nat := 1042248141557213089527755

theorem tailTrace_6089313 : CollatzResearch.WordTrace tailWord_6089313 prefixEnd_6089313 1042248141557213089527755 := by
  unfold tailWord_6089313
  simp only [CollatzResearch.WordTrace]
  refine ⟨222095490988466447709120593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148063660658977631806080395 222095490988466447709120593)
  ·
    refine ⟨166571618241349835781840445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222095490988466447709120593 166571618241349835781840445)
    ·
      refine ⟨62464356840506188418190167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166571618241349835781840445 62464356840506188418190167)
      ·
        refine ⟨93696535260759282627285251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62464356840506188418190167 93696535260759282627285251)
        ·
          refine ⟨140544802891138923940927877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93696535260759282627285251 140544802891138923940927877)
          ·
            refine ⟨26352150542088548238923977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140544802891138923940927877 26352150542088548238923977)
            ·
              refine ⟨19764112906566411179192983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26352150542088548238923977 19764112906566411179192983)
              ·
                refine ⟨29646169359849616768789475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19764112906566411179192983 29646169359849616768789475)
                ·
                  refine ⟨44469254039774425153184213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29646169359849616768789475 44469254039774425153184213)
                  ·
                    refine ⟨1042248141557213089527755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44469254039774425153184213 1042248141557213089527755)
                    ·
                      rfl

theorem cell23_6089313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_6089313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089313 prefixEnd_6089313 := by exact prefixLift 6089313
  have htrace : WordTrace (prefixWord ++ tailWord_6089313) baseStart_6089313 baseEnd_6089313 := by
    simpa [prefixWord, tailWord_6089313, baseEnd_6089313] using wordTrace_append hprefix tailTrace_6089313
  have hstable : (prefixWord ++ tailWord_6089313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089313).length < 2 ^ (prefixWord ++ tailWord_6089313).sum := by decide
  have hdescent : baseEnd_6089313 < baseStart_6089313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089334 : List Nat := [5, 1, 1, 2, 4, 1, 1, 1, 7]
def baseStart_6089334 : Nat := 118140960795 + 6089334 * 2 ^ 59
def prefixEnd_6089334 : Nat := 4983230072969 + 3 ^ 40 * 6089334 * 2
def baseEnd_6089334 : Nat := 347417245307264854046741

theorem tailTrace_6089334 : CollatzResearch.WordTrace tailWord_6089334 prefixEnd_6089334 347417245307264854046741 := by
  unfold tailWord_6089334
  simp only [CollatzResearch.WordTrace]
  refine ⟨13881016057586898018477191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148064171280926912197090037 13881016057586898018477191)
  ·
    refine ⟨20821524086380347027715787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13881016057586898018477191 20821524086380347027715787)
    ·
      refine ⟨31232286129570520541573681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20821524086380347027715787 31232286129570520541573681)
      ·
        refine ⟨23424214597177890406180261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31232286129570520541573681 23424214597177890406180261)
        ·
          refine ⟨4392040236970854451158799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23424214597177890406180261 4392040236970854451158799)
          ·
            refine ⟨6588060355456281676738199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4392040236970854451158799 6588060355456281676738199)
            ·
              refine ⟨9882090533184422515107299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6588060355456281676738199 9882090533184422515107299)
              ·
                refine ⟨14823135799776633772660949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9882090533184422515107299 14823135799776633772660949)
                ·
                  refine ⟨347417245307264854046741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14823135799776633772660949 347417245307264854046741)
                  ·
                    rfl

theorem cell23_6089334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_6089334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089334 prefixEnd_6089334 := by exact prefixLift 6089334
  have htrace : WordTrace (prefixWord ++ tailWord_6089334) baseStart_6089334 baseEnd_6089334 := by
    simpa [prefixWord, tailWord_6089334, baseEnd_6089334] using wordTrace_append hprefix tailTrace_6089334
  have hstable : (prefixWord ++ tailWord_6089334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089334).length < 2 ^ (prefixWord ++ tailWord_6089334).sum := by decide
  have hdescent : baseEnd_6089334 < baseStart_6089334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089373 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 10]
def baseStart_6089373 : Nat := 118140960795 + 6089373 * 2 ^ 59
def prefixEnd_6089373 : Nat := 4983230072969 + 3 ^ 40 * 6089373 * 2
def baseEnd_6089373 : Nat := 347419470390101003759221

theorem tailTrace_6089373 : CollatzResearch.WordTrace tailWord_6089373 prefixEnd_6089373 347419470390101003759221 := by
  unfold tailWord_6089373
  simp only [CollatzResearch.WordTrace]
  refine ⟨222097679368249077956304773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148065119578832718637536515 222097679368249077956304773)
  ·
    refine ⟨41643314881546702116807145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222097679368249077956304773 41643314881546702116807145)
    ·
      refine ⟨31232486161160026587605359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41643314881546702116807145 31232486161160026587605359)
      ·
        refine ⟨46848729241740039881408039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31232486161160026587605359 46848729241740039881408039)
        ·
          refine ⟨70273093862610059822112059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46848729241740039881408039 70273093862610059822112059)
          ·
            refine ⟨105409640793915089733168089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70273093862610059822112059 105409640793915089733168089)
            ·
              refine ⟨79057230595436317299876067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105409640793915089733168089 79057230595436317299876067)
              ·
                refine ⟨118585845893154475949814101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79057230595436317299876067 118585845893154475949814101)
                ·
                  refine ⟨347419470390101003759221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 118585845893154475949814101 347419470390101003759221)
                  ·
                    rfl

theorem cell23_6089373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 10].length) (baseStart_6089373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089373 prefixEnd_6089373 := by exact prefixLift 6089373
  have htrace : WordTrace (prefixWord ++ tailWord_6089373) baseStart_6089373 baseEnd_6089373 := by
    simpa [prefixWord, tailWord_6089373, baseEnd_6089373] using wordTrace_append hprefix tailTrace_6089373
  have hstable : (prefixWord ++ tailWord_6089373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089373).length < 2 ^ (prefixWord ++ tailWord_6089373).sum := by decide
  have hdescent : baseEnd_6089373 < baseStart_6089373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089463 : List Nat := [1, 1, 3, 1, 1, 1, 3, 12]
def baseStart_6089463 : Nat := 118140960795 + 6089463 * 2 ^ 59
def prefixEnd_6089463 : Nat := 4983230072969 + 3 ^ 40 * 6089463 * 2
def baseEnd_6089463 : Nat := 115808201732215321544725

theorem tailTrace_6089463 : CollatzResearch.WordTrace tailWord_6089463 prefixEnd_6089463 115808201732215321544725 := by
  unfold tailWord_6089463
  simp only [CollatzResearch.WordTrace]
  refine ⟨222100961937923023327081043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148067307958615348884720695 222100961937923023327081043)
  ·
    refine ⟨333151442906884534990621565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222100961937923023327081043 333151442906884534990621565)
    ·
      refine ⟨124931791090081700621483087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 333151442906884534990621565 124931791090081700621483087)
      ·
        refine ⟨187397686635122550932224631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124931791090081700621483087 187397686635122550932224631)
        ·
          refine ⟨281096529952683826398336947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187397686635122550932224631 281096529952683826398336947)
          ·
            refine ⟨421644794929025739597505421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281096529952683826398336947 421644794929025739597505421)
            ·
              refine ⟨158116798098384652349064533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 421644794929025739597505421 158116798098384652349064533)
              ·
                refine ⟨115808201732215321544725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 158116798098384652349064533 115808201732215321544725)
                ·
                  rfl

theorem cell23_6089463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 12].length) (baseStart_6089463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089463 prefixEnd_6089463 := by exact prefixLift 6089463
  have htrace : WordTrace (prefixWord ++ tailWord_6089463) baseStart_6089463 baseEnd_6089463 := by
    simpa [prefixWord, tailWord_6089463, baseEnd_6089463] using wordTrace_append hprefix tailTrace_6089463
  have hstable : (prefixWord ++ tailWord_6089463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089463).length < 2 ^ (prefixWord ++ tailWord_6089463).sum := by decide
  have hdescent : baseEnd_6089463 < baseStart_6089463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089474 : List Nat := [3, 4, 1, 1, 1, 2, 1, 4, 1, 1, 4]
def baseStart_6089474 : Nat := 118140960795 + 6089474 * 2 ^ 59
def prefixEnd_6089474 : Nat := 4983230072969 + 3 ^ 40 * 6089474 * 2
def baseEnd_6089474 : Nat := 3126827095057013138670025

theorem tailTrace_6089474 : CollatzResearch.WordTrace tailWord_6089474 prefixEnd_6089474 3126827095057013138670025 := by
  unfold tailWord_6089474
  simp only [CollatzResearch.WordTrace]
  refine ⟨55525340785220793051432869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148067575427255448137154317 55525340785220793051432869)
  ·
    refine ⟨10411001397228898697143663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55525340785220793051432869 10411001397228898697143663)
    ·
      refine ⟨15616502095843348045715495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10411001397228898697143663 15616502095843348045715495)
      ·
        refine ⟨23424753143765022068573243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15616502095843348045715495 23424753143765022068573243)
        ·
          refine ⟨35137129715647533102859865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23424753143765022068573243 35137129715647533102859865)
          ·
            refine ⟨26352847286735649827144899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35137129715647533102859865 26352847286735649827144899)
            ·
              refine ⟨39529270930103474740717349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26352847286735649827144899 39529270930103474740717349)
              ·
                refine ⟨7411738299394401513884503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39529270930103474740717349 7411738299394401513884503)
                ·
                  refine ⟨11117607449091602270826755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7411738299394401513884503 11117607449091602270826755)
                  ·
                    refine ⟨16676411173637403406240133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11117607449091602270826755 16676411173637403406240133)
                    ·
                      refine ⟨3126827095057013138670025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16676411173637403406240133 3126827095057013138670025)
                      ·
                        rfl

theorem cell23_6089474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_6089474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089474 prefixEnd_6089474 := by exact prefixLift 6089474
  have htrace : WordTrace (prefixWord ++ tailWord_6089474) baseStart_6089474 baseEnd_6089474 := by
    simpa [prefixWord, tailWord_6089474, baseEnd_6089474] using wordTrace_append hprefix tailTrace_6089474
  have hstable : (prefixWord ++ tailWord_6089474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089474).length < 2 ^ (prefixWord ++ tailWord_6089474).sum := by decide
  have hdescent : baseEnd_6089474 < baseStart_6089474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089480 : List Nat := [2, 1, 3, 2, 2, 3, 1, 9]
def baseStart_6089480 : Nat := 118140960795 + 6089480 * 2 ^ 59
def prefixEnd_6089480 : Nat := 4983230072969 + 3 ^ 40 * 6089480 * 2
def baseEnd_6089480 : Nat := 115808525034849633896111

theorem tailTrace_6089480 : CollatzResearch.WordTrace tailWord_6089480 prefixEnd_6089480 115808525034849633896111 := by
  unfold tailWord_6089480
  simp only [CollatzResearch.WordTrace]
  refine ⟨111050790989430717615224947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148067721319240956820299929 111050790989430717615224947)
  ·
    refine ⟨166576186484146076422837421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111050790989430717615224947 166576186484146076422837421)
    ·
      refine ⟨62466069931554778658564033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166576186484146076422837421 62466069931554778658564033)
      ·
        refine ⟨46849552448666083993923025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62466069931554778658564033 46849552448666083993923025)
        ·
          refine ⟨35137164336499562995442269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46849552448666083993923025 35137164336499562995442269)
          ·
            refine ⟨13176436626187336123290851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35137164336499562995442269 13176436626187336123290851)
            ·
              refine ⟨19764654939281004184936277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13176436626187336123290851 19764654939281004184936277)
              ·
                refine ⟨115808525034849633896111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19764654939281004184936277 115808525034849633896111)
                ·
                  rfl

theorem cell23_6089480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 9].length) (baseStart_6089480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089480 prefixEnd_6089480 := by exact prefixLift 6089480
  have htrace : WordTrace (prefixWord ++ tailWord_6089480) baseStart_6089480 baseEnd_6089480 := by
    simpa [prefixWord, tailWord_6089480, baseEnd_6089480] using wordTrace_append hprefix tailTrace_6089480
  have hstable : (prefixWord ++ tailWord_6089480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089480).length < 2 ^ (prefixWord ++ tailWord_6089480).sum := by decide
  have hdescent : baseEnd_6089480 < baseStart_6089480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089508 : List Nat := [2, 3, 1, 3, 3, 2, 1, 1, 3, 2, 2]
def baseStart_6089508 : Nat := 118140960795 + 6089508 * 2 ^ 59
def prefixEnd_6089508 : Nat := 4983230072969 + 3 ^ 40 * 6089508 * 2
def baseEnd_6089508 : Nat := 3126844553399266005644869

theorem tailTrace_6089508 : CollatzResearch.WordTrace tailWord_6089508 prefixEnd_6089508 3126844553399266005644869 := by
  unfold tailWord_6089508
  simp only [CollatzResearch.WordTrace]
  refine ⟨111051301611379998006234589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148068402148506664008312785 111051301611379998006234589)
  ·
    refine ⟨41644238104267499252337971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111051301611379998006234589 41644238104267499252337971)
    ·
      refine ⟨62466357156401248878506957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41644238104267499252337971 62466357156401248878506957)
      ·
        refine ⟨23424883933650468329440109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62466357156401248878506957 23424883933650468329440109)
        ·
          refine ⟨8784331475118925623540041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23424883933650468329440109 8784331475118925623540041)
          ·
            refine ⟨6588248606339194217655031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8784331475118925623540041 6588248606339194217655031)
            ·
              refine ⟨9882372909508791326482547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6588248606339194217655031 9882372909508791326482547)
              ·
                refine ⟨14823559364263186989723821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9882372909508791326482547 14823559364263186989723821)
                ·
                  refine ⟨5558834761598695121146433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14823559364263186989723821 5558834761598695121146433)
                  ·
                    refine ⟨4169126071199021340859825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5558834761598695121146433 4169126071199021340859825)
                    ·
                      refine ⟨3126844553399266005644869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4169126071199021340859825 3126844553399266005644869)
                      ·
                        rfl

theorem cell23_6089508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_6089508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089508 prefixEnd_6089508 := by exact prefixLift 6089508
  have htrace : WordTrace (prefixWord ++ tailWord_6089508) baseStart_6089508 baseEnd_6089508 := by
    simpa [prefixWord, tailWord_6089508, baseEnd_6089508] using wordTrace_append hprefix tailTrace_6089508
  have hstable : (prefixWord ++ tailWord_6089508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089508).length < 2 ^ (prefixWord ++ tailWord_6089508).sum := by decide
  have hdescent : baseEnd_6089508 < baseStart_6089508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089514 : List Nat := [3, 1, 4, 3, 1, 1, 2, 8]
def baseStart_6089514 : Nat := 118140960795 + 6089514 * 2 ^ 59
def prefixEnd_6089514 : Nat := 4983230072969 + 3 ^ 40 * 6089514 * 2
def baseEnd_6089514 : Nat := 115809171640118258598883

theorem tailTrace_6089514 : CollatzResearch.WordTrace tailWord_6089514 prefixEnd_6089514 115809171640118258598883 := by
  unfold tailWord_6089514
  simp only [CollatzResearch.WordTrace]
  refine ⟨55525705515184564759296899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148068548040492172691458397 55525705515184564759296899)
  ·
    refine ⟨83288558272776847138945349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55525705515184564759296899 83288558272776847138945349)
    ·
      refine ⟨15616604676145658838552253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83288558272776847138945349 15616604676145658838552253)
      ·
        refine ⟨5856226753554622064457095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15616604676145658838552253 5856226753554622064457095)
        ·
          refine ⟨8784340130331933096685643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5856226753554622064457095 8784340130331933096685643)
          ·
            refine ⟨13176510195497899645028465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8784340130331933096685643 13176510195497899645028465)
            ·
              refine ⟨9882382646623424733771349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13176510195497899645028465 9882382646623424733771349)
              ·
                refine ⟨115809171640118258598883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9882382646623424733771349 115809171640118258598883)
                ·
                  rfl

theorem cell23_6089514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 8].length) (baseStart_6089514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089514 prefixEnd_6089514 := by exact prefixLift 6089514
  have htrace : WordTrace (prefixWord ++ tailWord_6089514) baseStart_6089514 baseEnd_6089514 := by
    simpa [prefixWord, tailWord_6089514, baseEnd_6089514] using wordTrace_append hprefix tailTrace_6089514
  have hstable : (prefixWord ++ tailWord_6089514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089514).length < 2 ^ (prefixWord ++ tailWord_6089514).sum := by decide
  have hdescent : baseEnd_6089514 < baseStart_6089514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089518 : List Nat := [4, 1, 3, 2, 1, 3, 2, 1, 2, 4]
def baseStart_6089518 : Nat := 118140960795 + 6089518 * 2 ^ 59
def prefixEnd_6089518 : Nat := 4983230072969 + 3 ^ 40 * 6089518 * 2
def baseEnd_6089518 : Nat := 1042283229401936988839941

theorem tailTrace_6089518 : CollatzResearch.WordTrace tailWord_6089518 prefixEnd_6089518 1042283229401936988839941 := by
  unfold tailWord_6089518
  simp only [CollatzResearch.WordTrace]
  refine ⟨27762870994090470965041651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148068645301815845146888805 27762870994090470965041651)
  ·
    refine ⟨41644306491135706447562477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27762870994090470965041651 41644306491135706447562477)
    ·
      refine ⟨15616614934175889917835929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41644306491135706447562477 15616614934175889917835929)
      ·
        refine ⟨11712461200631917438376947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15616614934175889917835929 11712461200631917438376947)
        ·
          refine ⟨17568691800947876157565421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11712461200631917438376947 17568691800947876157565421)
          ·
            refine ⟨6588259425355453559087033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17568691800947876157565421 6588259425355453559087033)
            ·
              refine ⟨4941194569016590169315275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6588259425355453559087033 4941194569016590169315275)
              ·
                refine ⟨7411791853524885253972913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4941194569016590169315275 7411791853524885253972913)
                ·
                  refine ⟨5558843890143663940479685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7411791853524885253972913 5558843890143663940479685)
                  ·
                    refine ⟨1042283229401936988839941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5558843890143663940479685 1042283229401936988839941)
                    ·
                      rfl

theorem cell23_6089518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_6089518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089518 prefixEnd_6089518 := by exact prefixLift 6089518
  have htrace : WordTrace (prefixWord ++ tailWord_6089518) baseStart_6089518 baseEnd_6089518 := by
    simpa [prefixWord, tailWord_6089518, baseEnd_6089518] using wordTrace_append hprefix tailTrace_6089518
  have hstable : (prefixWord ++ tailWord_6089518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089518).length < 2 ^ (prefixWord ++ tailWord_6089518).sum := by decide
  have hdescent : baseEnd_6089518 < baseStart_6089518 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089560 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 3, 4, 4]
def baseStart_6089560 : Nat := 118140960795 + 6089560 * 2 ^ 59
def prefixEnd_6089560 : Nat := 4983230072969 + 3 ^ 40 * 6089560 * 2
def baseEnd_6089560 : Nat := 3126871254393299802194629

theorem tailTrace_6089560 : CollatzResearch.WordTrace tailWord_6089560 prefixEnd_6089560 3126871254393299802194629 := by
  unfold tailWord_6089560
  simp only [CollatzResearch.WordTrace]
  refine ⟨111052249909285804446681067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148069666545714405928908089 111052249909285804446681067)
  ·
    refine ⟨166578374863928706670021601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111052249909285804446681067 166578374863928706670021601)
    ·
      refine ⟨124933781147946530002516201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166578374863928706670021601 124933781147946530002516201)
      ·
        refine ⟨93700335860959897501887151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124933781147946530002516201 93700335860959897501887151)
        ·
          refine ⟨140550503791439846252830727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93700335860959897501887151 140550503791439846252830727)
          ·
            refine ⟨210825755687159769379246091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140550503791439846252830727 210825755687159769379246091)
            ·
              refine ⟨316238633530739654068869137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210825755687159769379246091 316238633530739654068869137)
              ·
                refine ⟨237178975148054740551651853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 316238633530739654068869137 237178975148054740551651853)
                ·
                  refine ⟨88942115680520527706869445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 237178975148054740551651853 88942115680520527706869445)
                  ·
                    refine ⟨16676646690097598945038021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 88942115680520527706869445 16676646690097598945038021)
                    ·
                      refine ⟨3126871254393299802194629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16676646690097598945038021 3126871254393299802194629)
                      ·
                        rfl

theorem cell23_6089560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_6089560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089560 prefixEnd_6089560 := by exact prefixLift 6089560
  have htrace : WordTrace (prefixWord ++ tailWord_6089560) baseStart_6089560 baseEnd_6089560 := by
    simpa [prefixWord, tailWord_6089560, baseEnd_6089560] using wordTrace_append hprefix tailTrace_6089560
  have hstable : (prefixWord ++ tailWord_6089560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089560).length < 2 ^ (prefixWord ++ tailWord_6089560).sum := by decide
  have hdescent : baseEnd_6089560 < baseStart_6089560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089647 : List Nat := [1, 1, 2, 1, 2, 2, 2, 3, 5, 4]
def baseStart_6089647 : Nat := 118140960795 + 6089647 * 2 ^ 59
def prefixEnd_6089647 : Nat := 4983230072969 + 3 ^ 40 * 6089647 * 2
def baseEnd_6089647 : Nat := 1042305309070080320602243

theorem tailTrace_6089647 : CollatzResearch.WordTrace tailWord_6089647 prefixEnd_6089647 1042305309070080320602243 := by
  unfold tailWord_6089647
  simp only [CollatzResearch.WordTrace]
  refine ⟨222107672969256422751779195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148071781979504281834519463 222107672969256422751779195)
  ·
    refine ⟨333161509453884634127668793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222107672969256422751779195 333161509453884634127668793)
    ·
      refine ⟨249871132090413475595751595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333161509453884634127668793 249871132090413475595751595)
      ·
        refine ⟨374806698135620213393627393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249871132090413475595751595 374806698135620213393627393)
        ·
          refine ⟨281105023601715160045220545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374806698135620213393627393 281105023601715160045220545)
          ·
            refine ⟨210828767701286370033915409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281105023601715160045220545 210828767701286370033915409)
            ·
              refine ⟨158121575775964777525436557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210828767701286370033915409 158121575775964777525436557)
              ·
                refine ⟨59295590915986791572038709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158121575775964777525436557 59295590915986791572038709)
                ·
                  refine ⟨5558961648373761709878629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59295590915986791572038709 5558961648373761709878629)
                  ·
                    refine ⟨1042305309070080320602243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5558961648373761709878629 1042305309070080320602243)
                    ·
                      rfl

theorem cell23_6089647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 5, 4].length) (baseStart_6089647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089647 prefixEnd_6089647 := by exact prefixLift 6089647
  have htrace : WordTrace (prefixWord ++ tailWord_6089647) baseStart_6089647 baseEnd_6089647 := by
    simpa [prefixWord, tailWord_6089647, baseEnd_6089647] using wordTrace_append hprefix tailTrace_6089647
  have hstable : (prefixWord ++ tailWord_6089647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089647).length < 2 ^ (prefixWord ++ tailWord_6089647).sum := by decide
  have hdescent : baseEnd_6089647 < baseStart_6089647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089687 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 2, 5, 3]
def baseStart_6089687 : Nat := 118140960795 + 6089687 * 2 ^ 59
def prefixEnd_6089687 : Nat := 4983230072969 + 3 ^ 40 * 6089687 * 2
def baseEnd_6089687 : Nat := 3126936466436420805306545

theorem tailTrace_6089687 : CollatzResearch.WordTrace tailWord_6089687 prefixEnd_6089687 3126936466436420805306545 := by
  unfold tailWord_6089687
  simp only [CollatzResearch.WordTrace]
  refine ⟨222109131889111509583235315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148072754592741006388823543 222109131889111509583235315)
  ·
    refine ⟨333163697833667264374852973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222109131889111509583235315 333163697833667264374852973)
    ·
      refine ⟨124936386687625224140569865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 333163697833667264374852973 124936386687625224140569865)
      ·
        refine ⟨93702290015718918105427399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124936386687625224140569865 93702290015718918105427399)
        ·
          refine ⟨140553435023578377158141099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93702290015718918105427399 140553435023578377158141099)
          ·
            refine ⟨210830152535367565737211649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140553435023578377158141099 210830152535367565737211649)
            ·
              refine ⟨158122614401525674302908737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210830152535367565737211649 158122614401525674302908737)
              ·
                refine ⟨118591960801144255727181553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158122614401525674302908737 118591960801144255727181553)
                ·
                  refine ⟨88943970600858191795386165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118591960801144255727181553 88943970600858191795386165)
                  ·
                    refine ⟨8338497243830455480817453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88943970600858191795386165 8338497243830455480817453)
                    ·
                      refine ⟨3126936466436420805306545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8338497243830455480817453 3126936466436420805306545)
                      ·
                        rfl

theorem cell23_6089687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 5, 3].length) (baseStart_6089687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089687 prefixEnd_6089687 := by exact prefixLift 6089687
  have htrace : WordTrace (prefixWord ++ tailWord_6089687) baseStart_6089687 baseEnd_6089687 := by
    simpa [prefixWord, tailWord_6089687, baseEnd_6089687] using wordTrace_append hprefix tailTrace_6089687
  have hstable : (prefixWord ++ tailWord_6089687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089687).length < 2 ^ (prefixWord ++ tailWord_6089687).sum := by decide
  have hdescent : baseEnd_6089687 < baseStart_6089687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089747 : List Nat := [1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 5]
def baseStart_6089747 : Nat := 118140960795 + 6089747 * 2 ^ 59
def prefixEnd_6089747 : Nat := 4983230072969 + 3 ^ 40 * 6089747 * 2
def baseEnd_6089747 : Nat := 3126967275275690570556269

theorem tailTrace_6089747 : CollatzResearch.WordTrace tailWord_6089747 prefixEnd_6089747 3126967275275690570556269 := by
  unfold tailWord_6089747
  simp only [CollatzResearch.WordTrace]
  refine ⟨222111320268894139830419495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148074213512596093220279663 222111320268894139830419495)
  ·
    refine ⟨333166980403341209745629243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222111320268894139830419495 333166980403341209745629243)
    ·
      refine ⟨499750470605011814618443865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333166980403341209745629243 499750470605011814618443865)
      ·
        refine ⟨374812852953758860963832899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 499750470605011814618443865 374812852953758860963832899)
        ·
          refine ⟨562219279430638291445749349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374812852953758860963832899 562219279430638291445749349)
          ·
            refine ⟨105416114893244679646078003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 562219279430638291445749349 105416114893244679646078003)
            ·
              refine ⟨158124172339867019469117005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105416114893244679646078003 158124172339867019469117005)
              ·
                refine ⟨59296564627450132300918877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158124172339867019469117005 59296564627450132300918877)
                ·
                  refine ⟨22236211735293799612844579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59296564627450132300918877 22236211735293799612844579)
                  ·
                    refine ⟨33354317602940699419266869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22236211735293799612844579 33354317602940699419266869)
                    ·
                      refine ⟨3126967275275690570556269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33354317602940699419266869 3126967275275690570556269)
                      ·
                        rfl

theorem cell23_6089747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 1, 5].length) (baseStart_6089747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089747 prefixEnd_6089747 := by exact prefixLift 6089747
  have htrace : WordTrace (prefixWord ++ tailWord_6089747) baseStart_6089747 baseEnd_6089747 := by
    simpa [prefixWord, tailWord_6089747, baseEnd_6089747] using wordTrace_append hprefix tailTrace_6089747
  have hstable : (prefixWord ++ tailWord_6089747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089747).length < 2 ^ (prefixWord ++ tailWord_6089747).sum := by decide
  have hdescent : baseEnd_6089747 < baseStart_6089747 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089754 : List Nat := [3, 1, 1, 3, 1, 2, 4, 1, 1, 6]
def baseStart_6089754 : Nat := 118140960795 + 6089754 * 2 ^ 59
def prefixEnd_6089754 : Nat := 4983230072969 + 3 ^ 40 * 6089754 * 2
def baseEnd_6089754 : Nat := 1042323623213424014389579

theorem tailTrace_6089754 : CollatzResearch.WordTrace tailWord_6089754 prefixEnd_6089754 1042323623213424014389579 := by
  unfold tailWord_6089754
  simp only [CollatzResearch.WordTrace]
  refine ⟨55527893894967195006481079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148074383719912520017282877 55527893894967195006481079)
  ·
    refine ⟨83291840842450792509721619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55527893894967195006481079 83291840842450792509721619)
    ·
      refine ⟨124937761263676188764582429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83291840842450792509721619 124937761263676188764582429)
      ·
        refine ⟨46851660473878570786718411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124937761263676188764582429 46851660473878570786718411)
        ·
          refine ⟨70277490710817856180077617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46851660473878570786718411 70277490710817856180077617)
          ·
            refine ⟨52708118033113392135058213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70277490710817856180077617 52708118033113392135058213)
            ·
              refine ⟨9882772131208761025323415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52708118033113392135058213 9882772131208761025323415)
              ·
                refine ⟨14824158196813141537985123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9882772131208761025323415 14824158196813141537985123)
                ·
                  refine ⟨22236237295219712306977685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14824158196813141537985123 22236237295219712306977685)
                  ·
                    refine ⟨1042323623213424014389579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22236237295219712306977685 1042323623213424014389579)
                    ·
                      rfl

theorem cell23_6089754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 1, 6].length) (baseStart_6089754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089754 prefixEnd_6089754 := by exact prefixLift 6089754
  have htrace : WordTrace (prefixWord ++ tailWord_6089754) baseStart_6089754 baseEnd_6089754 := by
    simpa [prefixWord, tailWord_6089754, baseEnd_6089754] using wordTrace_append hprefix tailTrace_6089754
  have hstable : (prefixWord ++ tailWord_6089754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089754).length < 2 ^ (prefixWord ++ tailWord_6089754).sum := by decide
  have hdescent : baseEnd_6089754 < baseStart_6089754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089788 : List Nat := [2, 2, 2, 2, 2, 4, 1, 2, 2, 4]
def baseStart_6089788 : Nat := 118140960795 + 6089788 * 2 ^ 59
def prefixEnd_6089788 : Nat := 4983230072969 + 3 ^ 40 * 6089788 * 2
def baseEnd_6089788 : Nat := 1042329442660841636714527

theorem tailTrace_6089788 : CollatzResearch.WordTrace tailWord_6089788 prefixEnd_6089788 1042329442660841636714527 := by
  unfold tailWord_6089788
  simp only [CollatzResearch.WordTrace]
  refine ⟨111056407830872801916331009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148075210441163735888441345 111056407830872801916331009)
  ·
    refine ⟨83292305873154601437248257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111056407830872801916331009 83292305873154601437248257)
    ·
      refine ⟨62469229404865951077936193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83292305873154601437248257 62469229404865951077936193)
      ·
        refine ⟨46851922053649463308452145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62469229404865951077936193 46851922053649463308452145)
        ·
          refine ⟨35138941540237097481339109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46851922053649463308452145 35138941540237097481339109)
          ·
            refine ⟨6588551538794455777751083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35138941540237097481339109 6588551538794455777751083)
            ·
              refine ⟨9882827308191683666626625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6588551538794455777751083 9882827308191683666626625)
              ·
                refine ⟨7412120481143762749969969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9882827308191683666626625 7412120481143762749969969)
                ·
                  refine ⟨5559090360857822062477477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7412120481143762749969969 5559090360857822062477477)
                  ·
                    refine ⟨1042329442660841636714527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5559090360857822062477477 1042329442660841636714527)
                    ·
                      rfl

theorem cell23_6089788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 2, 4].length) (baseStart_6089788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089788 prefixEnd_6089788 := by exact prefixLift 6089788
  have htrace : WordTrace (prefixWord ++ tailWord_6089788) baseStart_6089788 baseEnd_6089788 := by
    simpa [prefixWord, tailWord_6089788, baseEnd_6089788] using wordTrace_append hprefix tailTrace_6089788
  have hstable : (prefixWord ++ tailWord_6089788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089788).length < 2 ^ (prefixWord ++ tailWord_6089788).sum := by decide
  have hdescent : baseEnd_6089788 < baseStart_6089788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089797 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 1, 9]
def baseStart_6089797 : Nat := 118140960795 + 6089797 * 2 ^ 59
def prefixEnd_6089797 : Nat := 4983230072969 + 3 ^ 40 * 6089797 * 2
def baseEnd_6089797 : Nat := 1042330983102805124977013

theorem tailTrace_6089797 : CollatzResearch.WordTrace tailWord_6089797 prefixEnd_6089797 1042330983102805124977013 := by
  unfold tailWord_6089797
  simp only [CollatzResearch.WordTrace]
  refine ⟨222113143918712998369739645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148075429279141998913159763 222113143918712998369739645)
  ·
    refine ⟨83292428969517374388652367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222113143918712998369739645 83292428969517374388652367)
    ·
      refine ⟨124938643454276061582978551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83292428969517374388652367 124938643454276061582978551)
      ·
        refine ⟨187407965181414092374467827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124938643454276061582978551 187407965181414092374467827)
        ·
          refine ⟨281111947772121138561701741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187407965181414092374467827 281111947772121138561701741)
          ·
            refine ⟨105416980414545426960638153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 281111947772121138561701741 105416980414545426960638153)
            ·
              refine ⟨79062735310909070220478615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105416980414545426960638153 79062735310909070220478615)
              ·
                refine ⟨118594102966363605330717923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79062735310909070220478615 118594102966363605330717923)
                ·
                  refine ⟨177891154449545407996076885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118594102966363605330717923 177891154449545407996076885)
                  ·
                    refine ⟨1042330983102805124977013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 177891154449545407996076885 1042330983102805124977013)
                    ·
                      rfl

theorem cell23_6089797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 9].length) (baseStart_6089797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089797 prefixEnd_6089797 := by exact prefixLift 6089797
  have htrace : WordTrace (prefixWord ++ tailWord_6089797) baseStart_6089797 baseEnd_6089797 := by
    simpa [prefixWord, tailWord_6089797, baseEnd_6089797] using wordTrace_append hprefix tailTrace_6089797
  have hstable : (prefixWord ++ tailWord_6089797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089797).length < 2 ^ (prefixWord ++ tailWord_6089797).sum := by decide
  have hdescent : baseEnd_6089797 < baseStart_6089797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089798 : List Nat := [6, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5]
def baseStart_6089798 : Nat := 118140960795 + 6089798 * 2 ^ 59
def prefixEnd_6089798 : Nat := 4983230072969 + 3 ^ 40 * 6089798 * 2
def baseEnd_6089798 : Nat := 3126993462789069871018535

theorem tailTrace_6089798 : CollatzResearch.WordTrace tailWord_6089798 prefixEnd_6089798 3126993462789069871018535 := by
  unfold tailWord_6089798
  simp only [CollatzResearch.WordTrace]
  refine ⟨6941036887240917985641439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 148075453594472917027017365 6941036887240917985641439)
  ·
    refine ⟨10411555330861376978462159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6941036887240917985641439 10411555330861376978462159)
    ·
      refine ⟨15617332996292065467693239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10411555330861376978462159 15617332996292065467693239)
      ·
        refine ⟨23425999494438098201539859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15617332996292065467693239 23425999494438098201539859)
        ·
          refine ⟨35138999241657147302309789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23425999494438098201539859 35138999241657147302309789)
          ·
            refine ⟨13177124715621430238366171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35138999241657147302309789 13177124715621430238366171)
            ·
              refine ⟨19765687073432145357549257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13177124715621430238366171 19765687073432145357549257)
              ·
                refine ⟨14824265305074109018161943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19765687073432145357549257 14824265305074109018161943)
                ·
                  refine ⟨22236397957611163527242915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14824265305074109018161943 22236397957611163527242915)
                  ·
                    refine ⟨33354596936416745290864373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22236397957611163527242915 33354596936416745290864373)
                    ·
                      refine ⟨3126993462789069871018535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33354596936416745290864373 3126993462789069871018535)
                      ·
                        rfl

theorem cell23_6089798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_6089798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089798 prefixEnd_6089798 := by exact prefixLift 6089798
  have htrace : WordTrace (prefixWord ++ tailWord_6089798) baseStart_6089798 baseEnd_6089798 := by
    simpa [prefixWord, tailWord_6089798, baseEnd_6089798] using wordTrace_append hprefix tailTrace_6089798
  have hstable : (prefixWord ++ tailWord_6089798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089798).length < 2 ^ (prefixWord ++ tailWord_6089798).sum := by decide
  have hdescent : baseEnd_6089798 < baseStart_6089798 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089805 : List Nat := [1, 6, 1, 1, 1, 3, 3, 1, 2, 4]
def baseStart_6089805 : Nat := 118140960795 + 6089805 * 2 ^ 59
def prefixEnd_6089805 : Nat := 4983230072969 + 3 ^ 40 * 6089805 * 2
def baseEnd_6089805 : Nat := 1042332352384550447877001

theorem tailTrace_6089805 : CollatzResearch.WordTrace tailWord_6089805 prefixEnd_6089805 1042332352384550447877001 := by
  unfold tailWord_6089805
  simp only [CollatzResearch.WordTrace]
  refine ⟨222113435702684015736030869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148075623801789343824020579 222113435702684015736030869)
  ·
    refine ⟨10411567298563313237626447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 222113435702684015736030869 10411567298563313237626447)
    ·
      refine ⟨15617350947844969856439671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10411567298563313237626447 15617350947844969856439671)
      ·
        refine ⟨23426026421767454784659507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15617350947844969856439671 23426026421767454784659507)
        ·
          refine ⟨35139039632651182176989261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23426026421767454784659507 35139039632651182176989261)
          ·
            refine ⟨13177139862244193316370973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35139039632651182176989261 13177139862244193316370973)
            ·
              refine ⟨4941427448341572493639115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13177139862244193316370973 4941427448341572493639115)
              ·
                refine ⟨7412141172512358740458673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4941427448341572493639115 7412141172512358740458673)
                ·
                  refine ⟨5559105879384269055344005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7412141172512358740458673 5559105879384269055344005)
                  ·
                    refine ⟨1042332352384550447877001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5559105879384269055344005 1042332352384550447877001)
                    ·
                      rfl

theorem cell23_6089805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_6089805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089805 prefixEnd_6089805 := by exact prefixLift 6089805
  have htrace : WordTrace (prefixWord ++ tailWord_6089805) baseStart_6089805 baseEnd_6089805 := by
    simpa [prefixWord, tailWord_6089805, baseEnd_6089805] using wordTrace_append hprefix tailTrace_6089805
  have hstable : (prefixWord ++ tailWord_6089805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089805).length < 2 ^ (prefixWord ++ tailWord_6089805).sum := by decide
  have hdescent : baseEnd_6089805 < baseStart_6089805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089807 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 5]
def baseStart_6089807 : Nat := 118140960795 + 6089807 * 2 ^ 59
def prefixEnd_6089807 : Nat := 4983230072969 + 3 ^ 40 * 6089807 * 2
def baseEnd_6089807 : Nat := 3126998084114960335805993

theorem tailTrace_6089807 : CollatzResearch.WordTrace tailWord_6089807 prefixEnd_6089807 3126998084114960335805993 := by
  unfold tailWord_6089807
  simp only [CollatzResearch.WordTrace]
  refine ⟨222113508648676770077603675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148075672432451180051735783 222113508648676770077603675)
  ·
    refine ⟨333170262973015155116405513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222113508648676770077603675 333170262973015155116405513)
    ·
      refine ⟨249877697229761366337304135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333170262973015155116405513 249877697229761366337304135)
      ·
        refine ⟨374816545844642049505956203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249877697229761366337304135 374816545844642049505956203)
        ·
          refine ⟨562224818766963074258934305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374816545844642049505956203 562224818766963074258934305)
          ·
            refine ⟨421668614075222305694200729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 562224818766963074258934305 421668614075222305694200729)
            ·
              refine ⟨316251460556416729270650547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 421668614075222305694200729 316251460556416729270650547)
              ·
                refine ⟨474377190834625093905975821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 316251460556416729270650547 474377190834625093905975821)
                ·
                  refine ⟨177891446562984410214740933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 474377190834625093905975821 177891446562984410214740933)
                  ·
                    refine ⟨33354646230559576915263925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 177891446562984410214740933 33354646230559576915263925)
                    ·
                      refine ⟨3126998084114960335805993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33354646230559576915263925 3126998084114960335805993)
                      ·
                        rfl

theorem cell23_6089807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 5].length) (baseStart_6089807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089807 prefixEnd_6089807 := by exact prefixLift 6089807
  have htrace : WordTrace (prefixWord ++ tailWord_6089807) baseStart_6089807 baseEnd_6089807 := by
    simpa [prefixWord, tailWord_6089807, baseEnd_6089807] using wordTrace_append hprefix tailTrace_6089807
  have hstable : (prefixWord ++ tailWord_6089807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089807).length < 2 ^ (prefixWord ++ tailWord_6089807).sum := by decide
  have hdescent : baseEnd_6089807 < baseStart_6089807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089817 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 1, 2, 8]
def baseStart_6089817 : Nat := 118140960795 + 6089817 * 2 ^ 59
def prefixEnd_6089817 : Nat := 4983230072969 + 3 ^ 40 * 6089817 * 2
def baseEnd_6089817 : Nat := 3127003218921505296680947

theorem tailTrace_6089817 : CollatzResearch.WordTrace tailWord_6089817 prefixEnd_6089817 3127003218921505296680947 := by
  unfold tailWord_6089817
  simp only [CollatzResearch.WordTrace]
  refine ⟨222113873378640541785467705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148075915585760361190311803 222113873378640541785467705)
  ·
    refine ⟨166585405033980406339100779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222113873378640541785467705 166585405033980406339100779)
    ·
      refine ⟨249878107550970609508651169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166585405033980406339100779 249878107550970609508651169)
      ·
        refine ⟨187408580663227957131488377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249878107550970609508651169 187408580663227957131488377)
        ·
          refine ⟨140556435497420967848616283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187408580663227957131488377 140556435497420967848616283)
          ·
            refine ⟨210834653246131451772924425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140556435497420967848616283 210834653246131451772924425)
            ·
              refine ⟨158125989934598588829693319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210834653246131451772924425 158125989934598588829693319)
              ·
                refine ⟨237188984901897883244539979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158125989934598588829693319 237188984901897883244539979)
                ·
                  refine ⟨355783477352846824866809969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 237188984901897883244539979 355783477352846824866809969)
                  ·
                    refine ⟨266837608014635118650107477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 355783477352846824866809969 266837608014635118650107477)
                    ·
                      refine ⟨3127003218921505296680947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 266837608014635118650107477 3127003218921505296680947)
                      ·
                        rfl

theorem cell23_6089817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_6089817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089817 prefixEnd_6089817 := by exact prefixLift 6089817
  have htrace : WordTrace (prefixWord ++ tailWord_6089817) baseStart_6089817 baseEnd_6089817 := by
    simpa [prefixWord, tailWord_6089817, baseEnd_6089817] using wordTrace_append hprefix tailTrace_6089817
  have hstable : (prefixWord ++ tailWord_6089817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089817).length < 2 ^ (prefixWord ++ tailWord_6089817).sum := by decide
  have hdescent : baseEnd_6089817 < baseStart_6089817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089911 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 1, 7, 2]
def baseStart_6089911 : Nat := 118140960795 + 6089911 * 2 ^ 59
def prefixEnd_6089911 : Nat := 4983230072969 + 3 ^ 40 * 6089911 * 2
def baseEnd_6089911 : Nat := 3127051486103027928905515

theorem tailTrace_6089911 : CollatzResearch.WordTrace tailWord_6089911 prefixEnd_6089911 3127051486103027928905515 := by
  unfold tailWord_6089911
  simp only [CollatzResearch.WordTrace]
  refine ⟨222117301840299995839389587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148078201226866663892926391 222117301840299995839389587)
  ·
    refine ⟨333175952760449993759084381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222117301840299995839389587 333175952760449993759084381)
    ·
      refine ⟨124940982285168747659656643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 333175952760449993759084381 124940982285168747659656643)
      ·
        refine ⟨187411473427753121489484965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124940982285168747659656643 187411473427753121489484965)
        ·
          refine ⟨35139651267703710279278431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 187411473427753121489484965 35139651267703710279278431)
          ·
            refine ⟨52709476901555565418917647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35139651267703710279278431 52709476901555565418917647)
            ·
              refine ⟨79064215352333348128376471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52709476901555565418917647 79064215352333348128376471)
              ·
                refine ⟨118596323028500022192564707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79064215352333348128376471 118596323028500022192564707)
                ·
                  refine ⟨177894484542750033288847061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118596323028500022192564707 177894484542750033288847061)
                  ·
                    refine ⟨4169401981470703905207353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 177894484542750033288847061 4169401981470703905207353)
                    ·
                      refine ⟨3127051486103027928905515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4169401981470703905207353 3127051486103027928905515)
                      ·
                        rfl

theorem cell23_6089911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 7, 2].length) (baseStart_6089911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089911 prefixEnd_6089911 := by exact prefixLift 6089911
  have htrace : WordTrace (prefixWord ++ tailWord_6089911) baseStart_6089911 baseEnd_6089911 := by
    simpa [prefixWord, tailWord_6089911, baseEnd_6089911] using wordTrace_append hprefix tailTrace_6089911
  have hstable : (prefixWord ++ tailWord_6089911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089911).length < 2 ^ (prefixWord ++ tailWord_6089911).sum := by decide
  have hdescent : baseEnd_6089911 < baseStart_6089911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089918 : List Nat := [4, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3]
def baseStart_6089918 : Nat := 118140960795 + 6089918 * 2 ^ 59
def prefixEnd_6089918 : Nat := 4983230072969 + 3 ^ 40 * 6089918 * 2
def baseEnd_6089918 : Nat := 3127055080467609401517983

theorem tailTrace_6089918 : CollatzResearch.WordTrace tailWord_6089918 prefixEnd_6089918 3127055080467609401517983 := by
  unfold tailWord_6089918
  simp only [CollatzResearch.WordTrace]
  refine ⟨27764694643909329504361801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148078371434183090689929605 27764694643909329504361801)
  ·
    refine ⟨20823520982931997128271351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27764694643909329504361801 20823520982931997128271351)
    ·
      refine ⟨31235281474397995692407027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20823520982931997128271351 31235281474397995692407027)
      ·
        refine ⟨46852922211596993538610541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31235281474397995692407027 46852922211596993538610541)
        ·
          refine ⟨17569845829348872576978953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46852922211596993538610541 17569845829348872576978953)
          ·
            refine ⟨13177384372011654432734215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17569845829348872576978953 13177384372011654432734215)
            ·
              refine ⟨19766076558017481649101323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13177384372011654432734215 19766076558017481649101323)
              ·
                refine ⟨29649114837026222473651985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19766076558017481649101323 29649114837026222473651985)
                ·
                  refine ⟨22236836127769666855238989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29649114837026222473651985 22236836127769666855238989)
                  ·
                    refine ⟨8338813547913625070714621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22236836127769666855238989 8338813547913625070714621)
                    ·
                      refine ⟨3127055080467609401517983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8338813547913625070714621 3127055080467609401517983)
                      ·
                        rfl

theorem cell23_6089918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_6089918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089918 prefixEnd_6089918 := by exact prefixLift 6089918
  have htrace : WordTrace (prefixWord ++ tailWord_6089918) baseStart_6089918 baseEnd_6089918 := by
    simpa [prefixWord, tailWord_6089918, baseEnd_6089918] using wordTrace_append hprefix tailTrace_6089918
  have hstable : (prefixWord ++ tailWord_6089918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089918).length < 2 ^ (prefixWord ++ tailWord_6089918).sum := by decide
  have hdescent : baseEnd_6089918 < baseStart_6089918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089942 : List Nat := [5, 2, 1, 2, 2, 1, 2, 3, 5]
def baseStart_6089942 : Nat := 118140960795 + 6089942 * 2 ^ 59
def prefixEnd_6089942 : Nat := 4983230072969 + 3 ^ 40 * 6089942 * 2
def baseEnd_6089942 : Nat := 347451933778146367513097

theorem tailTrace_6089942 : CollatzResearch.WordTrace tailWord_6089942 prefixEnd_6089942 347451933778146367513097 := by
  unfold tailWord_6089942
  simp only [CollatzResearch.WordTrace]
  refine ⟨13882402031449230508360505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148078955002125125422512053 13882402031449230508360505)
  ·
    refine ⟨10411801523586922881270379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13882402031449230508360505 10411801523586922881270379)
    ·
      refine ⟨15617702285380384321905569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10411801523586922881270379 15617702285380384321905569)
      ·
        refine ⟨11713276714035288241429177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15617702285380384321905569 11713276714035288241429177)
        ·
          refine ⟨8784957535526466181071883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11713276714035288241429177 8784957535526466181071883)
          ·
            refine ⟨13177436303289699271607825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8784957535526466181071883 13177436303289699271607825)
            ·
              refine ⟨9883077227467274453705869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13177436303289699271607825 9883077227467274453705869)
              ·
                refine ⟨3706153960300227920139701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9883077227467274453705869 3706153960300227920139701)
                ·
                  refine ⟨347451933778146367513097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3706153960300227920139701 347451933778146367513097)
                  ·
                    rfl

theorem cell23_6089942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_6089942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089942 prefixEnd_6089942 := by exact prefixLift 6089942
  have htrace : WordTrace (prefixWord ++ tailWord_6089942) baseStart_6089942 baseEnd_6089942 := by
    simpa [prefixWord, tailWord_6089942, baseEnd_6089942] using wordTrace_append hprefix tailTrace_6089942
  have hstable : (prefixWord ++ tailWord_6089942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089942).length < 2 ^ (prefixWord ++ tailWord_6089942).sum := by decide
  have hdescent : baseEnd_6089942 < baseStart_6089942 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6089984 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 6]
def baseStart_6089984 : Nat := 118140960795 + 6089984 * 2 ^ 59
def prefixEnd_6089984 : Nat := 4983230072969 + 3 ^ 40 * 6089984 * 2
def baseEnd_6089984 : Nat := 3127088970190806143292679

theorem tailTrace_6089984 : CollatzResearch.WordTrace tailWord_6089984 prefixEnd_6089984 3127088970190806143292679 := by
  unfold tailWord_6089984
  simp only [CollatzResearch.WordTrace]
  refine ⟨111059982184517764653398503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148079976246023686204531337 111059982184517764653398503)
  ·
    refine ⟨166589973276776646980097755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111059982184517764653398503 166589973276776646980097755)
    ·
      refine ⟨249884959915164970470146633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166589973276776646980097755 249884959915164970470146633)
      ·
        refine ⟨187413719936373727852609975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249884959915164970470146633 187413719936373727852609975)
        ·
          refine ⟨281120579904560591778914963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187413719936373727852609975 281120579904560591778914963)
          ·
            refine ⟨421680869856840887668372445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281120579904560591778914963 421680869856840887668372445)
            ·
              refine ⟨158130326196315332875639667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 421680869856840887668372445 158130326196315332875639667)
              ·
                refine ⟨237195489294472999313459501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158130326196315332875639667 237195489294472999313459501)
                ·
                  refine ⟨88948308485427374742547313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 237195489294472999313459501 88948308485427374742547313)
                  ·
                    refine ⟨66711231364070531056910485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88948308485427374742547313 66711231364070531056910485)
                    ·
                      refine ⟨3127088970190806143292679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66711231364070531056910485 3127088970190806143292679)
                      ·
                        rfl

theorem cell23_6089984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_6089984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6089984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6089984 prefixEnd_6089984 := by exact prefixLift 6089984
  have htrace : WordTrace (prefixWord ++ tailWord_6089984) baseStart_6089984 baseEnd_6089984 := by
    simpa [prefixWord, tailWord_6089984, baseEnd_6089984] using wordTrace_append hprefix tailTrace_6089984
  have hstable : (prefixWord ++ tailWord_6089984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6089984).length < 2 ^ (prefixWord ++ tailWord_6089984).sum := by decide
  have hdescent : baseEnd_6089984 < baseStart_6089984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6089984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090031 : List Nat := [1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 4]
def baseStart_6090031 : Nat := 118140960795 + 6090031 * 2 ^ 59
def prefixEnd_6090031 : Nat := 4983230072969 + 3 ^ 40 * 6090031 * 2
def baseEnd_6090031 : Nat := 3127113103781567459404963

theorem tailTrace_6090031 : CollatzResearch.WordTrace tailWord_6090031 prefixEnd_6090031 3127113103781567459404963 := by
  unfold tailWord_6090031
  simp only [CollatzResearch.WordTrace]
  refine ⟨222121678599865256333757947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148081119066576837555838631 222121678599865256333757947)
  ·
    refine ⟨333182517899797884500636921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222121678599865256333757947 333182517899797884500636921)
    ·
      refine ⟨249886888424848413375477691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333182517899797884500636921 249886888424848413375477691)
      ·
        refine ⟨374830332637272620063216537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249886888424848413375477691 374830332637272620063216537)
        ·
          refine ⟨281122749477954465047412403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374830332637272620063216537 281122749477954465047412403)
          ·
            refine ⟨421684124216931697571118605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281122749477954465047412403 421684124216931697571118605)
            ·
              refine ⟨158131546581349386589169477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 421684124216931697571118605 158131546581349386589169477)
              ·
                refine ⟨29649664984003009985469277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158131546581349386589169477 29649664984003009985469277)
                ·
                  refine ⟨11118624369001128744550979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29649664984003009985469277 11118624369001128744550979)
                  ·
                    refine ⟨16677936553501693116826469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11118624369001128744550979 16677936553501693116826469)
                    ·
                      refine ⟨3127113103781567459404963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16677936553501693116826469 3127113103781567459404963)
                      ·
                        rfl

theorem cell23_6090031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 1, 4].length) (baseStart_6090031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090031 prefixEnd_6090031 := by exact prefixLift 6090031
  have htrace : WordTrace (prefixWord ++ tailWord_6090031) baseStart_6090031 baseEnd_6090031 := by
    simpa [prefixWord, tailWord_6090031, baseEnd_6090031] using wordTrace_append hprefix tailTrace_6090031
  have hstable : (prefixWord ++ tailWord_6090031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090031).length < 2 ^ (prefixWord ++ tailWord_6090031).sum := by decide
  have hdescent : baseEnd_6090031 < baseStart_6090031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090045 : List Nat := [1, 4, 1, 5, 1, 1, 1, 1, 3, 5]
def baseStart_6090045 : Nat := 118140960795 + 6090045 * 2 ^ 59
def prefixEnd_6090045 : Nat := 4983230072969 + 3 ^ 40 * 6090045 * 2
def baseEnd_6090045 : Nat := 1042373430836910134876633

theorem tailTrace_6090045 : CollatzResearch.WordTrace tailWord_6090045 prefixEnd_6090045 1042373430836910134876633 := by
  unfold tailWord_6090045
  simp only [CollatzResearch.WordTrace]
  refine ⟨222122189221814536724767589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148081459481209691149845059 222122189221814536724767589)
  ·
    refine ⟨41647910479090225635893923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222122189221814536724767589 41647910479090225635893923)
    ·
      refine ⟨62471865718635338453840885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41647910479090225635893923 62471865718635338453840885)
      ·
        refine ⟨5856737411122062980047583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62471865718635338453840885 5856737411122062980047583)
        ·
          refine ⟨8785106116683094470071375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5856737411122062980047583 8785106116683094470071375)
          ·
            refine ⟨13177659175024641705107063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8785106116683094470071375 13177659175024641705107063)
            ·
              refine ⟨19766488762536962557660595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13177659175024641705107063 19766488762536962557660595)
              ·
                refine ⟨29649733143805443836490893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19766488762536962557660595 29649733143805443836490893)
                ·
                  refine ⟨11118649928927041438684085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29649733143805443836490893 11118649928927041438684085)
                  ·
                    refine ⟨1042373430836910134876633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11118649928927041438684085 1042373430836910134876633)
                    ·
                      rfl

theorem cell23_6090045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 3, 5].length) (baseStart_6090045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090045 prefixEnd_6090045 := by exact prefixLift 6090045
  have htrace : WordTrace (prefixWord ++ tailWord_6090045) baseStart_6090045 baseEnd_6090045 := by
    simpa [prefixWord, tailWord_6090045, baseEnd_6090045] using wordTrace_append hprefix tailTrace_6090045
  have hstable : (prefixWord ++ tailWord_6090045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090045).length < 2 ^ (prefixWord ++ tailWord_6090045).sum := by decide
  have hdescent : baseEnd_6090045 < baseStart_6090045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090052 : List Nat := [2, 3, 4, 1, 1, 1, 1, 3, 2, 3, 2]
def baseStart_6090052 : Nat := 118140960795 + 6090052 * 2 ^ 59
def prefixEnd_6090052 : Nat := 4983230072969 + 3 ^ 40 * 6090052 * 2
def baseEnd_6090052 : Nat := 3127123886875311877242367

theorem tailTrace_6090052 : CollatzResearch.WordTrace tailWord_6090052 prefixEnd_6090052 3127123886875311877242367 := by
  unfold tailWord_6090052
  simp only [CollatzResearch.WordTrace]
  refine ⟨111061222266394588460136205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148081629688526117946848273 111061222266394588460136205)
  ·
    refine ⟨41647958349897970672551077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111061222266394588460136205 41647958349897970672551077)
    ·
      refine ⟨7808992190605869501103327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41647958349897970672551077 7808992190605869501103327)
      ·
        refine ⟨11713488285908804251654991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7808992190605869501103327 11713488285908804251654991)
        ·
          refine ⟨17570232428863206377482487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11713488285908804251654991 17570232428863206377482487)
          ·
            refine ⟨26355348643294809566223731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17570232428863206377482487 26355348643294809566223731)
            ·
              refine ⟨39533022964942214349335597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26355348643294809566223731 39533022964942214349335597)
              ·
                refine ⟨14824883611853330381000849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39533022964942214349335597 14824883611853330381000849)
                ·
                  refine ⟨11118662708889997785750637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14824883611853330381000849 11118662708889997785750637)
                  ·
                    refine ⟨4169498515833749169656489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11118662708889997785750637 4169498515833749169656489)
                    ·
                      refine ⟨3127123886875311877242367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4169498515833749169656489 3127123886875311877242367)
                      ·
                        rfl

theorem cell23_6090052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_6090052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090052 prefixEnd_6090052 := by exact prefixLift 6090052
  have htrace : WordTrace (prefixWord ++ tailWord_6090052) baseStart_6090052 baseEnd_6090052 := by
    simpa [prefixWord, tailWord_6090052, baseEnd_6090052] using wordTrace_append hprefix tailTrace_6090052
  have hstable : (prefixWord ++ tailWord_6090052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090052).length < 2 ^ (prefixWord ++ tailWord_6090052).sum := by decide
  have hdescent : baseEnd_6090052 < baseStart_6090052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090065 : List Nat := [1, 2, 2, 1, 4, 1, 5, 1, 1, 1, 4]
def baseStart_6090065 : Nat := 118140960795 + 6090065 * 2 ^ 59
def prefixEnd_6090065 : Nat := 4983230072969 + 3 ^ 40 * 6090065 * 2
def baseEnd_6090065 : Nat := 3127130562123820326379807

theorem tailTrace_6090065 : CollatzResearch.WordTrace tailWord_6090065 prefixEnd_6090065 3127130562123820326379807 := by
  unfold tailWord_6090065
  simp only [CollatzResearch.WordTrace]
  refine ⟨222122918681742080140495649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148081945787828053426997099 222122918681742080140495649)
  ·
    refine ⟨166592189011306560105371737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222122918681742080140495649 166592189011306560105371737)
    ·
      refine ⟨124944141758479920079028803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166592189011306560105371737 124944141758479920079028803)
      ·
        refine ⟨187416212637719880118543205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124944141758479920079028803 187416212637719880118543205)
        ·
          refine ⟨35140539869572477522226851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 187416212637719880118543205 35140539869572477522226851)
          ·
            refine ⟨52710809804358716283340277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35140539869572477522226851 52710809804358716283340277)
            ·
              refine ⟨4941638419158629651563151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52710809804358716283340277 4941638419158629651563151)
              ·
                refine ⟨7412457628737944477344727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4941638419158629651563151 7412457628737944477344727)
                ·
                  refine ⟨11118686443106916716017091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7412457628737944477344727 11118686443106916716017091)
                  ·
                    refine ⟨16678029664660375074025637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11118686443106916716017091 16678029664660375074025637)
                    ·
                      refine ⟨3127130562123820326379807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16678029664660375074025637 3127130562123820326379807)
                      ·
                        rfl

theorem cell23_6090065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 1, 1, 4].length) (baseStart_6090065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090065 prefixEnd_6090065 := by exact prefixLift 6090065
  have htrace : WordTrace (prefixWord ++ tailWord_6090065) baseStart_6090065 baseEnd_6090065 := by
    simpa [prefixWord, tailWord_6090065, baseEnd_6090065] using wordTrace_append hprefix tailTrace_6090065
  have hstable : (prefixWord ++ tailWord_6090065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090065).length < 2 ^ (prefixWord ++ tailWord_6090065).sum := by decide
  have hdescent : baseEnd_6090065 < baseStart_6090065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090070 : List Nat := [5, 2, 3, 1, 1, 2, 2, 2, 1, 4]
def baseStart_6090070 : Nat := 118140960795 + 6090070 * 2 ^ 59
def prefixEnd_6090070 : Nat := 4983230072969 + 3 ^ 40 * 6090070 * 2
def baseEnd_6090070 : Nat := 1042377709842364268939095

theorem tailTrace_6090070 : CollatzResearch.WordTrace tailWord_6090070 prefixEnd_6090070 1042377709842364268939095 := by
  unfold tailWord_6090070
  simp only [CollatzResearch.WordTrace]
  refine ⟨13882693815420247874651729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148082067364482643996285109 13882693815420247874651729)
  ·
    refine ⟨10412020361565185905988797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13882693815420247874651729 10412020361565185905988797)
    ·
      refine ⟨3904507635586944714745799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10412020361565185905988797 3904507635586944714745799)
      ·
        refine ⟨5856761453380417072118699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3904507635586944714745799 5856761453380417072118699)
        ·
          refine ⟨8785142180070625608178049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5856761453380417072118699 8785142180070625608178049)
          ·
            refine ⟨6588856635052969206133537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8785142180070625608178049 6588856635052969206133537)
            ·
              refine ⟨4941642476289726904600153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6588856635052969206133537 4941642476289726904600153)
              ·
                refine ⟨3706231857217295178450115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4941642476289726904600153 3706231857217295178450115)
                ·
                  refine ⟨5559347785825942767675173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3706231857217295178450115 5559347785825942767675173)
                  ·
                    refine ⟨1042377709842364268939095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5559347785825942767675173 1042377709842364268939095)
                    ·
                      rfl

theorem cell23_6090070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_6090070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090070 prefixEnd_6090070 := by exact prefixLift 6090070
  have htrace : WordTrace (prefixWord ++ tailWord_6090070) baseStart_6090070 baseEnd_6090070 := by
    simpa [prefixWord, tailWord_6090070, baseEnd_6090070] using wordTrace_append hprefix tailTrace_6090070
  have hstable : (prefixWord ++ tailWord_6090070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090070).length < 2 ^ (prefixWord ++ tailWord_6090070).sum := by decide
  have hdescent : baseEnd_6090070 < baseStart_6090070 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090082 : List Nat := [3, 3, 2, 1, 1, 1, 2, 3, 3, 2, 2]
def baseStart_6090082 : Nat := 118140960795 + 6090082 * 2 ^ 59
def prefixEnd_6090082 : Nat := 4983230072969 + 3 ^ 40 * 6090082 * 2
def baseEnd_6090082 : Nat := 3127139291294946759867229

theorem tailTrace_6090082 : CollatzResearch.WordTrace tailWord_6090082 prefixEnd_6090082 3127139291294946759867229 := by
  unfold tailWord_6090082
  simp only [CollatzResearch.WordTrace]
  refine ⟨55530884680670123010966125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148082359148453661362576333 55530884680670123010966125)
  ·
    refine ⟨20824081755251296129112297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55530884680670123010966125 20824081755251296129112297)
    ·
      refine ⟨15618061316438472096834223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20824081755251296129112297 15618061316438472096834223)
      ·
        refine ⟨23427091974657708145251335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15618061316438472096834223 23427091974657708145251335)
        ·
          refine ⟨35140637961986562217877003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23427091974657708145251335 35140637961986562217877003)
          ·
            refine ⟨52710956942979843326815505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35140637961986562217877003 52710956942979843326815505)
            ·
              refine ⟨39533217707234882495111629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52710956942979843326815505 39533217707234882495111629)
              ·
                refine ⟨14824956640213080935666861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39533217707234882495111629 14824956640213080935666861)
                ·
                  refine ⟨5559358740079905350875073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14824956640213080935666861 5559358740079905350875073)
                  ·
                    refine ⟨4169519055059929013156305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5559358740079905350875073 4169519055059929013156305)
                    ·
                      refine ⟨3127139291294946759867229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4169519055059929013156305 3127139291294946759867229)
                      ·
                        rfl

theorem cell23_6090082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_6090082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090082 prefixEnd_6090082 := by exact prefixLift 6090082
  have htrace : WordTrace (prefixWord ++ tailWord_6090082) baseStart_6090082 baseEnd_6090082 := by
    simpa [prefixWord, tailWord_6090082, baseEnd_6090082] using wordTrace_append hprefix tailTrace_6090082
  have hstable : (prefixWord ++ tailWord_6090082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090082).length < 2 ^ (prefixWord ++ tailWord_6090082).sum := by decide
  have hdescent : baseEnd_6090082 < baseStart_6090082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090132 : List Nat := [2, 4, 2, 1, 2, 2, 1, 1, 4, 1, 3]
def baseStart_6090132 : Nat := 118140960795 + 6090132 * 2 ^ 59
def prefixEnd_6090132 : Nat := 4983230072969 + 3 ^ 40 * 6090132 * 2
def baseEnd_6090132 : Nat := 3127164965327671564241999

theorem tailTrace_6090132 : CollatzResearch.WordTrace tailWord_6090132 prefixEnd_6090132 3127164965327671564241999 := by
  unfold tailWord_6090132
  simp only [CollatzResearch.WordTrace]
  refine ⟨111062681186249675291592325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148083574914999567055456433 111062681186249675291592325)
  ·
    refine ⟨20824252722421814117173561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111062681186249675291592325 20824252722421814117173561)
    ·
      refine ⟨15618189541816360587880171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20824252722421814117173561 15618189541816360587880171)
      ·
        refine ⟨23427284312724540881820257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15618189541816360587880171 23427284312724540881820257)
        ·
          refine ⟨17570463234543405661365193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23427284312724540881820257 17570463234543405661365193)
          ·
            refine ⟨13177847425907554246023895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17570463234543405661365193 13177847425907554246023895)
            ·
              refine ⟨19766771138861331369035843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13177847425907554246023895 19766771138861331369035843)
              ·
                refine ⟨29650156708291997053553765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19766771138861331369035843 29650156708291997053553765)
                ·
                  refine ⟨5559404382804749447541331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29650156708291997053553765 5559404382804749447541331)
                  ·
                    refine ⟨8339106574207124171311997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5559404382804749447541331 8339106574207124171311997)
                    ·
                      refine ⟨3127164965327671564241999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8339106574207124171311997 3127164965327671564241999)
                      ·
                        rfl

theorem cell23_6090132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_6090132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090132 prefixEnd_6090132 := by exact prefixLift 6090132
  have htrace : WordTrace (prefixWord ++ tailWord_6090132) baseStart_6090132 baseEnd_6090132 := by
    simpa [prefixWord, tailWord_6090132, baseEnd_6090132] using wordTrace_append hprefix tailTrace_6090132
  have hstable : (prefixWord ++ tailWord_6090132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090132).length < 2 ^ (prefixWord ++ tailWord_6090132).sum := by decide
  have hdescent : baseEnd_6090132 < baseStart_6090132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090181 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 1, 6, 6]
def baseStart_6090181 : Nat := 118140960795 + 6090181 * 2 ^ 59
def prefixEnd_6090181 : Nat := 4983230072969 + 3 ^ 40 * 6090181 * 2
def baseEnd_6090181 : Nat := 3127190125879741872529273

theorem tailTrace_6090181 : CollatzResearch.WordTrace tailWord_6090181 prefixEnd_6090181 3127190125879741872529273 := by
  unfold tailWord_6090181
  simp only [CollatzResearch.WordTrace]
  refine ⟨222127149549321831951718397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148084766366214554634478931 222127149549321831951718397)
  ·
    refine ⟨83297681080995686981894399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222127149549321831951718397 83297681080995686981894399)
    ·
      refine ⟨124946521621493530472841599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83297681080995686981894399 124946521621493530472841599)
      ·
        refine ⟨187419782432240295709262399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124946521621493530472841599 187419782432240295709262399)
        ·
          refine ⟨281129673648360443563893599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187419782432240295709262399 281129673648360443563893599)
          ·
            refine ⟨421694510472540665345840399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281129673648360443563893599 421694510472540665345840399)
            ·
              refine ⟨632541765708810998018760599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 421694510472540665345840399 632541765708810998018760599)
              ·
                refine ⟨948812648563216497028140899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 632541765708810998018760599 948812648563216497028140899)
                ·
                  refine ⟨1423218972844824745542211349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 948812648563216497028140899 1423218972844824745542211349)
                  ·
                    refine ⟨66713389352101159947291157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1423218972844824745542211349 66713389352101159947291157)
                    ·
                      refine ⟨3127190125879741872529273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66713389352101159947291157 3127190125879741872529273)
                      ·
                        rfl

theorem cell23_6090181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_6090181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090181 prefixEnd_6090181 := by exact prefixLift 6090181
  have htrace : WordTrace (prefixWord ++ tailWord_6090181) baseStart_6090181 baseEnd_6090181 := by
    simpa [prefixWord, tailWord_6090181, baseEnd_6090181] using wordTrace_append hprefix tailTrace_6090181
  have hstable : (prefixWord ++ tailWord_6090181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090181).length < 2 ^ (prefixWord ++ tailWord_6090181).sum := by decide
  have hdescent : baseEnd_6090181 < baseStart_6090181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090225 : List Nat := [1, 2, 2, 2, 3, 3, 2, 1, 2, 5]
def baseStart_6090225 : Nat := 118140960795 + 6090225 * 2 ^ 59
def prefixEnd_6090225 : Nat := 4983230072969 + 3 ^ 40 * 6090225 * 2
def baseEnd_6090225 : Nat := 1042404239676179900126357

theorem tailTrace_6090225 : CollatzResearch.WordTrace tailWord_6090225 prefixEnd_6090225 1042404239676179900126357 := by
  unfold tailWord_6090225
  simp only [CollatzResearch.WordTrace]
  refine ⟨222128754361162427466320129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148085836240774951644213419 222128754361162427466320129)
  ·
    refine ⟨166596565770871820599740097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222128754361162427466320129 166596565770871820599740097)
    ·
      refine ⟨124947424328153865449805073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166596565770871820599740097 124947424328153865449805073)
      ·
        refine ⟨93710568246115399087353805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124947424328153865449805073 93710568246115399087353805)
        ·
          refine ⟨35141463092293274657757677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93710568246115399087353805 35141463092293274657757677)
          ·
            refine ⟨13178048659609977996659129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35141463092293274657757677 13178048659609977996659129)
            ·
              refine ⟨9883536494707483497494347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13178048659609977996659129 9883536494707483497494347)
              ·
                refine ⟨14825304742061225246241521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9883536494707483497494347 14825304742061225246241521)
                ·
                  refine ⟨11118978556545918934681141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14825304742061225246241521 11118978556545918934681141)
                  ·
                    refine ⟨1042404239676179900126357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11118978556545918934681141 1042404239676179900126357)
                    ·
                      rfl

theorem cell23_6090225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 2, 5].length) (baseStart_6090225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090225 prefixEnd_6090225 := by exact prefixLift 6090225
  have htrace : WordTrace (prefixWord ++ tailWord_6090225) baseStart_6090225 baseEnd_6090225 := by
    simpa [prefixWord, tailWord_6090225, baseEnd_6090225] using wordTrace_append hprefix tailTrace_6090225
  have hstable : (prefixWord ++ tailWord_6090225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090225).length < 2 ^ (prefixWord ++ tailWord_6090225).sum := by decide
  have hdescent : baseEnd_6090225 < baseStart_6090225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090242 : List Nat := [3, 4, 1, 2, 1, 1, 2, 2, 2, 5]
def baseStart_6090242 : Nat := 118140960795 + 6090242 * 2 ^ 59
def prefixEnd_6090242 : Nat := 4983230072969 + 3 ^ 40 * 6090242 * 2
def baseEnd_6090242 : Nat := 1042407149399888711288831

theorem tailTrace_6090242 : CollatzResearch.WordTrace tailWord_6090242 prefixEnd_6090242 1042407149399888711288831 := by
  unfold tailWord_6090242
  simp only [CollatzResearch.WordTrace]
  refine ⟨55532343600525209842422245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148086249601400559579792653 55532343600525209842422245)
  ·
    refine ⟨10412314425098476845454171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55532343600525209842422245 10412314425098476845454171)
    ·
      refine ⟨15618471637647715268181257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10412314425098476845454171 15618471637647715268181257)
      ·
        refine ⟨11713853728235786451135943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15618471637647715268181257 11713853728235786451135943)
        ·
          refine ⟨17570780592353679676703915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11713853728235786451135943 17570780592353679676703915)
          ·
            refine ⟨26356170888530519515055873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17570780592353679676703915 26356170888530519515055873)
            ·
              refine ⟨19767128166397889636291905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26356170888530519515055873 19767128166397889636291905)
              ·
                refine ⟨14825346124798417227218929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19767128166397889636291905 14825346124798417227218929)
                ·
                  refine ⟨11119009593598812920414197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14825346124798417227218929 11119009593598812920414197)
                  ·
                    refine ⟨1042407149399888711288831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11119009593598812920414197 1042407149399888711288831)
                    ·
                      rfl

theorem cell23_6090242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_6090242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090242 prefixEnd_6090242 := by exact prefixLift 6090242
  have htrace : WordTrace (prefixWord ++ tailWord_6090242) baseStart_6090242 baseEnd_6090242 := by
    simpa [prefixWord, tailWord_6090242, baseEnd_6090242] using wordTrace_append hprefix tailTrace_6090242
  have hstable : (prefixWord ++ tailWord_6090242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090242).length < 2 ^ (prefixWord ++ tailWord_6090242).sum := by decide
  have hdescent : baseEnd_6090242 < baseStart_6090242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090245 : List Nat := [1, 3, 1, 1, 2, 2, 1, 4, 2, 4, 2]
def baseStart_6090245 : Nat := 118140960795 + 6090245 * 2 ^ 59
def prefixEnd_6090245 : Nat := 4983230072969 + 3 ^ 40 * 6090245 * 2
def baseEnd_6090245 : Nat := 3127222988641629622128979

theorem tailTrace_6090245 : CollatzResearch.WordTrace tailWord_6090245 prefixEnd_6090245 3127222988641629622128979 := by
  unfold tailWord_6090245
  simp only [CollatzResearch.WordTrace]
  refine ⟨222129483821089970882048189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148086322547393313921365459 222129483821089970882048189)
  ·
    refine ⟨83298556432908739080768071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222129483821089970882048189 83298556432908739080768071)
    ·
      refine ⟨124947834649363108621152107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83298556432908739080768071 124947834649363108621152107)
      ·
        refine ⟨187421751974044662931728161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124947834649363108621152107 187421751974044662931728161)
        ·
          refine ⟨140566313980533497198796121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187421751974044662931728161 140566313980533497198796121)
          ·
            refine ⟨105424735485400122899097091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140566313980533497198796121 105424735485400122899097091)
            ·
              refine ⟨158137103228100184348645637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105424735485400122899097091 158137103228100184348645637)
              ·
                refine ⟨29650706855268784565371057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158137103228100184348645637 29650706855268784565371057)
                ·
                  refine ⟨22238030141451588424028293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29650706855268784565371057 22238030141451588424028293)
                  ·
                    refine ⟨4169630651522172829505305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22238030141451588424028293 4169630651522172829505305)
                    ·
                      refine ⟨3127222988641629622128979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4169630651522172829505305 3127222988641629622128979)
                      ·
                        rfl

theorem cell23_6090245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 2, 4, 2].length) (baseStart_6090245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090245 prefixEnd_6090245 := by exact prefixLift 6090245
  have htrace : WordTrace (prefixWord ++ tailWord_6090245) baseStart_6090245 baseEnd_6090245 := by
    simpa [prefixWord, tailWord_6090245, baseEnd_6090245] using wordTrace_append hprefix tailTrace_6090245
  have hstable : (prefixWord ++ tailWord_6090245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090245).length < 2 ^ (prefixWord ++ tailWord_6090245).sum := by decide
  have hdescent : baseEnd_6090245 < baseStart_6090245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090272 : List Nat := [2, 1, 1, 6, 1, 2, 1, 2, 3, 4]
def baseStart_6090272 : Nat := 118140960795 + 6090272 * 2 ^ 59
def prefixEnd_6090272 : Nat := 4983230072969 + 3 ^ 40 * 6090272 * 2
def baseEnd_6090272 : Nat := 1042412284206433672163785

theorem tailTrace_6090272 : CollatzResearch.WordTrace tailWord_6090272 prefixEnd_6090272 1042412284206433672163785 := by
  unfold tailWord_6090272
  simp only [CollatzResearch.WordTrace]
  refine ⟨111065234295996077246640535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148086979061328102995520713 111065234295996077246640535)
  ·
    refine ⟨166597851443994115869960803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111065234295996077246640535 166597851443994115869960803)
    ·
      refine ⟨249896777165991173804941205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166597851443994115869960803 249896777165991173804941205)
      ·
        refine ⟨11713911429655836272106619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 249896777165991173804941205 11713911429655836272106619)
        ·
          refine ⟨17570867144483754408159929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11713911429655836272106619 17570867144483754408159929)
          ·
            refine ⟨13178150358362815806119947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17570867144483754408159929 13178150358362815806119947)
            ·
              refine ⟨19767225537544223709179921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13178150358362815806119947 19767225537544223709179921)
              ·
                refine ⟨14825419153158167781884941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19767225537544223709179921 14825419153158167781884941)
                ·
                  refine ⟨5559532182434312918206853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14825419153158167781884941 5559532182434312918206853)
                  ·
                    refine ⟨1042412284206433672163785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5559532182434312918206853 1042412284206433672163785)
                    ·
                      rfl

theorem cell23_6090272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 3, 4].length) (baseStart_6090272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090272 prefixEnd_6090272 := by exact prefixLift 6090272
  have htrace : WordTrace (prefixWord ++ tailWord_6090272) baseStart_6090272 baseEnd_6090272 := by
    simpa [prefixWord, tailWord_6090272, baseEnd_6090272] using wordTrace_append hprefix tailTrace_6090272
  have hstable : (prefixWord ++ tailWord_6090272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090272).length < 2 ^ (prefixWord ++ tailWord_6090272).sum := by decide
  have hdescent : baseEnd_6090272 < baseStart_6090272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090322 : List Nat := [3, 2, 2, 1, 2, 2, 1, 2, 1, 5, 2]
def baseStart_6090322 : Nat := 118140960795 + 6090322 * 2 ^ 59
def prefixEnd_6090322 : Nat := 4983230072969 + 3 ^ 40 * 6090322 * 2
def baseEnd_6090322 : Nat := 3127262526652025820866125

theorem tailTrace_6090322 : CollatzResearch.WordTrace tailWord_6090322 prefixEnd_6090322 3127262526652025820866125 := by
  unfold tailWord_6090322
  simp only [CollatzResearch.WordTrace]
  refine ⟨55533073060452753258150305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148088194827874008688400813 55533073060452753258150305)
  ·
    refine ⟨41649804795339564943612729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55533073060452753258150305 41649804795339564943612729)
    ·
      refine ⟨31237353596504673707709547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41649804795339564943612729 31237353596504673707709547)
      ·
        refine ⟨46856030394757010561564321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31237353596504673707709547 46856030394757010561564321)
        ·
          refine ⟨35142022796067757921173241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46856030394757010561564321 35142022796067757921173241)
          ·
            refine ⟨26356517097050818440879931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35142022796067757921173241 26356517097050818440879931)
            ·
              refine ⟨39534775645576227661319897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26356517097050818440879931 39534775645576227661319897)
              ·
                refine ⟨29651081734182170745989923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39534775645576227661319897 29651081734182170745989923)
                ·
                  refine ⟨44476622601273256118984885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29651081734182170745989923 44476622601273256118984885)
                  ·
                    refine ⟨4169683368869367761154833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44476622601273256118984885 4169683368869367761154833)
                    ·
                      refine ⟨3127262526652025820866125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4169683368869367761154833 3127262526652025820866125)
                      ·
                        rfl

theorem cell23_6090322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_6090322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090322 prefixEnd_6090322 := by exact prefixLift 6090322
  have htrace : WordTrace (prefixWord ++ tailWord_6090322) baseStart_6090322 baseEnd_6090322 := by
    simpa [prefixWord, tailWord_6090322, baseEnd_6090322] using wordTrace_append hprefix tailTrace_6090322
  have hstable : (prefixWord ++ tailWord_6090322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090322).length < 2 ^ (prefixWord ++ tailWord_6090322).sum := by decide
  have hdescent : baseEnd_6090322 < baseStart_6090322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090332 : List Nat := [2, 2, 4, 1, 2, 1, 1, 4, 1, 5]
def baseStart_6090332 : Nat := 118140960795 + 6090332 * 2 ^ 59
def prefixEnd_6090332 : Nat := 4983230072969 + 3 ^ 40 * 6090332 * 2
def baseEnd_6090332 : Nat := 1042422553819523593913693

theorem tailTrace_6090332 : CollatzResearch.WordTrace tailWord_6090332 prefixEnd_6090332 1042422553819523593913693 := by
  unfold tailWord_6090332
  simp only [CollatzResearch.WordTrace]
  refine ⟨111066328485887392370232625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148088437981183189826976833 111066328485887392370232625)
  ·
    refine ⟨83299746364415544277674469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111066328485887392370232625 83299746364415544277674469)
    ·
      refine ⟨15618702443327914552063963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83299746364415544277674469 15618702443327914552063963)
      ·
        refine ⟨23428053664991871828095945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15618702443327914552063963 23428053664991871828095945)
        ·
          refine ⟨17571040248743903871071959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23428053664991871828095945 17571040248743903871071959)
          ·
            refine ⟨26356560373115855806607939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17571040248743903871071959 26356560373115855806607939)
            ·
              refine ⟨39534840559673783709911909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26356560373115855806607939 39534840559673783709911909)
              ·
                refine ⟨7412782604938834445608483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39534840559673783709911909 7412782604938834445608483)
                ·
                  refine ⟨11119173907408251668412725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7412782604938834445608483 11119173907408251668412725)
                  ·
                    refine ⟨1042422553819523593913693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11119173907408251668412725 1042422553819523593913693)
                    ·
                      rfl

theorem cell23_6090332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_6090332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090332 prefixEnd_6090332 := by exact prefixLift 6090332
  have htrace : WordTrace (prefixWord ++ tailWord_6090332) baseStart_6090332 baseEnd_6090332 := by
    simpa [prefixWord, tailWord_6090332, baseEnd_6090332] using wordTrace_append hprefix tailTrace_6090332
  have hstable : (prefixWord ++ tailWord_6090332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090332).length < 2 ^ (prefixWord ++ tailWord_6090332).sum := by decide
  have hdescent : baseEnd_6090332 < baseStart_6090332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090345 : List Nat := [1, 2, 1, 1, 1, 4, 3, 2, 4, 4]
def baseStart_6090345 : Nat := 118140960795 + 6090345 * 2 ^ 59
def prefixEnd_6090345 : Nat := 4983230072969 + 3 ^ 40 * 6090345 * 2
def baseEnd_6090345 : Nat := 1042424778902359743626173

theorem tailTrace_6090345 : CollatzResearch.WordTrace tailWord_6090345 prefixEnd_6090345 1042424778902359743626173 := by
  unfold tailWord_6090345
  simp only [CollatzResearch.WordTrace]
  refine ⟨222133131120727687960688489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148088754080485125307125659 222133131120727687960688489)
  ·
    refine ⟨166599848340545765970516367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222133131120727687960688489 166599848340545765970516367)
    ·
      refine ⟨249899772510818648955774551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166599848340545765970516367 249899772510818648955774551)
      ·
        refine ⟨374849658766227973433661827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249899772510818648955774551 374849658766227973433661827)
        ·
          refine ⟨562274488149341960150492741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374849658766227973433661827 562274488149341960150492741)
          ·
            refine ⟨105426466528001617528217389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 562274488149341960150492741 105426466528001617528217389)
            ·
              refine ⟨39534924948000606573081521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105426466528001617528217389 39534924948000606573081521)
              ·
                refine ⟨29651193711000454929811141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39534924948000606573081521 29651193711000454929811141)
                ·
                  refine ⟨5559598820812585299339589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29651193711000454929811141 5559598820812585299339589)
                  ·
                    refine ⟨1042424778902359743626173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5559598820812585299339589 1042424778902359743626173)
                    ·
                      rfl

theorem cell23_6090345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 4, 4].length) (baseStart_6090345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090345 prefixEnd_6090345 := by exact prefixLift 6090345
  have htrace : WordTrace (prefixWord ++ tailWord_6090345) baseStart_6090345 baseEnd_6090345 := by
    simpa [prefixWord, tailWord_6090345, baseEnd_6090345] using wordTrace_append hprefix tailTrace_6090345
  have hstable : (prefixWord ++ tailWord_6090345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090345).length < 2 ^ (prefixWord ++ tailWord_6090345).sum := by decide
  have hdescent : baseEnd_6090345 < baseStart_6090345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090346 : List Nat := [3, 1, 3, 2, 1, 2, 3, 3, 1, 1, 3]
def baseStart_6090346 : Nat := 118140960795 + 6090346 * 2 ^ 59
def prefixEnd_6090346 : Nat := 4983230072969 + 3 ^ 40 * 6090346 * 2
def baseEnd_6090346 : Nat := 3127274850187733726966015

theorem tailTrace_6090346 : CollatzResearch.WordTrace tailWord_6090346 prefixEnd_6090346 3127274850187733726966015 := by
  unfold tailWord_6090346
  simp only [CollatzResearch.WordTrace]
  refine ⟨55533291898431016282868723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148088778395816043420983261 55533291898431016282868723)
  ·
    refine ⟨83299937847646524424303085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55533291898431016282868723 83299937847646524424303085)
    ·
      refine ⟨31237476692867446659113657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83299937847646524424303085 31237476692867446659113657)
      ·
        refine ⟨23428107519650584994335243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31237476692867446659113657 23428107519650584994335243)
        ·
          refine ⟨35142161279475877491502865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23428107519650584994335243 35142161279475877491502865)
          ·
            refine ⟨26356620959606908118627149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35142161279475877491502865 26356620959606908118627149)
            ·
              refine ⟨9883732859852590544485181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26356620959606908118627149 9883732859852590544485181)
              ·
                refine ⟨3706399822444721454181943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9883732859852590544485181 3706399822444721454181943)
                ·
                  refine ⟨5559599733667082181272915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3706399822444721454181943 5559599733667082181272915)
                  ·
                    refine ⟨8339399600500623271909373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5559599733667082181272915 8339399600500623271909373)
                    ·
                      refine ⟨3127274850187733726966015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8339399600500623271909373 3127274850187733726966015)
                      ·
                        rfl

theorem cell23_6090346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_6090346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090346 prefixEnd_6090346 := by exact prefixLift 6090346
  have htrace : WordTrace (prefixWord ++ tailWord_6090346) baseStart_6090346 baseEnd_6090346 := by
    simpa [prefixWord, tailWord_6090346, baseEnd_6090346] using wordTrace_append hprefix tailTrace_6090346
  have hstable : (prefixWord ++ tailWord_6090346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090346).length < 2 ^ (prefixWord ++ tailWord_6090346).sum := by decide
  have hdescent : baseEnd_6090346 < baseStart_6090346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090352 : List Nat := [2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 4]
def baseStart_6090352 : Nat := 118140960795 + 6090352 * 2 ^ 59
def prefixEnd_6090352 : Nat := 4983230072969 + 3 ^ 40 * 6090352 * 2
def baseEnd_6090352 : Nat := 3127277931071660703490987

theorem tailTrace_6090352 : CollatzResearch.WordTrace tailWord_6090352 prefixEnd_6090352 3127277931071660703490987 := by
  unfold tailWord_6090352
  simp only [CollatzResearch.WordTrace]
  refine ⟨111066693215851164078096655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148088924287801552104128873 111066693215851164078096655)
  ·
    refine ⟨166600039823776746117144983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111066693215851164078096655 166600039823776746117144983)
    ·
      refine ⟨249900059735665119175717475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166600039823776746117144983 249900059735665119175717475)
      ·
        refine ⟨374850089603497678763576213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249900059735665119175717475 374850089603497678763576213)
        ·
          refine ⟨17571097950163953692042635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 374850089603497678763576213 17571097950163953692042635)
          ·
            refine ⟨26356646925245930538063953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17571097950163953692042635 26356646925245930538063953)
            ·
              refine ⟨19767485193934447903547965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26356646925245930538063953 19767485193934447903547965)
              ·
                refine ⟨7412806947725417963830487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19767485193934447903547965 7412806947725417963830487)
                ·
                  refine ⟨11119210421588126945745731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7412806947725417963830487 11119210421588126945745731)
                  ·
                    refine ⟨16678815632382190418618597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11119210421588126945745731 16678815632382190418618597)
                    ·
                      refine ⟨3127277931071660703490987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16678815632382190418618597 3127277931071660703490987)
                      ·
                        rfl

theorem cell23_6090352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 4].length) (baseStart_6090352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090352 prefixEnd_6090352 := by exact prefixLift 6090352
  have htrace : WordTrace (prefixWord ++ tailWord_6090352) baseStart_6090352 baseEnd_6090352 := by
    simpa [prefixWord, tailWord_6090352, baseEnd_6090352] using wordTrace_append hprefix tailTrace_6090352
  have hstable : (prefixWord ++ tailWord_6090352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090352).length < 2 ^ (prefixWord ++ tailWord_6090352).sum := by decide
  have hdescent : baseEnd_6090352 < baseStart_6090352 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090365 : List Nat := [1, 4, 1, 1, 4, 1, 1, 2, 1, 1, 6]
def baseStart_6090365 : Nat := 118140960795 + 6090365 * 2 ^ 59
def prefixEnd_6090365 : Nat := 4983230072969 + 3 ^ 40 * 6090365 * 2
def baseEnd_6090365 : Nat := 3127284606320169152628427

theorem tailTrace_6090365 : CollatzResearch.WordTrace tailWord_6090365 prefixEnd_6090365 3127284606320169152628427 := by
  unfold tailWord_6090365
  simp only [CollatzResearch.WordTrace]
  refine ⟨222133860580655231376416549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148089240387103487584277699 222133860580655231376416549)
  ·
    refine ⟨41650098858872855883078103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222133860580655231376416549 41650098858872855883078103)
    ·
      refine ⟨62475148288309283824617155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41650098858872855883078103 62475148288309283824617155)
      ·
        refine ⟨93712722432463925736925733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62475148288309283824617155 93712722432463925736925733)
        ·
          refine ⟨17571135456086986075673575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93712722432463925736925733 17571135456086986075673575)
          ·
            refine ⟨26356703184130479113510363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17571135456086986075673575 26356703184130479113510363)
            ·
              refine ⟨39535054776195718670265545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26356703184130479113510363 39535054776195718670265545)
              ·
                refine ⟨29651291082146789002699159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39535054776195718670265545 29651291082146789002699159)
                ·
                  refine ⟨44476936623220183504048739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29651291082146789002699159 44476936623220183504048739)
                  ·
                    refine ⟨66715404934830275256073109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44476936623220183504048739 66715404934830275256073109)
                    ·
                      refine ⟨3127284606320169152628427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66715404934830275256073109 3127284606320169152628427)
                      ·
                        rfl

theorem cell23_6090365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_6090365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090365 prefixEnd_6090365 := by exact prefixLift 6090365
  have htrace : WordTrace (prefixWord ++ tailWord_6090365) baseStart_6090365 baseEnd_6090365 := by
    simpa [prefixWord, tailWord_6090365, baseEnd_6090365] using wordTrace_append hprefix tailTrace_6090365
  have hstable : (prefixWord ++ tailWord_6090365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090365).length < 2 ^ (prefixWord ++ tailWord_6090365).sum := by decide
  have hdescent : baseEnd_6090365 < baseStart_6090365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090375 : List Nat := [1, 1, 4, 2, 1, 4, 2, 8]
def baseStart_6090375 : Nat := 118140960795 + 6090375 * 2 ^ 59
def prefixEnd_6090375 : Nat := 4983230072969 + 3 ^ 40 * 6090375 * 2
def baseEnd_6090375 : Nat := 115825545967656078277903

theorem tailTrace_6090375 : CollatzResearch.WordTrace tailWord_6090375 prefixEnd_6090375 115825545967656078277903 := by
  unfold tailWord_6090375
  simp only [CollatzResearch.WordTrace]
  refine ⟨222134225310619003084280579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148089483540412668722853719 222134225310619003084280579)
  ·
    refine ⟨333201337965928504626420869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222134225310619003084280579 333201337965928504626420869)
    ·
      refine ⟨62475250868611594617453913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 333201337965928504626420869 62475250868611594617453913)
      ·
        refine ⟨46856438151458695963090435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62475250868611594617453913 46856438151458695963090435)
        ·
          refine ⟨70284657227188043944635653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46856438151458695963090435 70284657227188043944635653)
          ·
            refine ⟨13178373230097758239619185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70284657227188043944635653 13178373230097758239619185)
            ·
              refine ⟨9883779922573318679714389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13178373230097758239619185 9883779922573318679714389)
              ·
                refine ⟨115825545967656078277903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9883779922573318679714389 115825545967656078277903)
                ·
                  rfl

theorem cell23_6090375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 8].length) (baseStart_6090375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090375 prefixEnd_6090375 := by exact prefixLift 6090375
  have htrace : WordTrace (prefixWord ++ tailWord_6090375) baseStart_6090375 baseEnd_6090375 := by
    simpa [prefixWord, tailWord_6090375, baseEnd_6090375] using wordTrace_append hprefix tailTrace_6090375
  have hstable : (prefixWord ++ tailWord_6090375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090375).length < 2 ^ (prefixWord ++ tailWord_6090375).sum := by decide
  have hdescent : baseEnd_6090375 < baseStart_6090375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090386 : List Nat := [3, 2, 3, 1, 3, 2, 1, 2, 1, 1, 4]
def baseStart_6090386 : Nat := 118140960795 + 6090386 * 2 ^ 59
def prefixEnd_6090386 : Nat := 4983230072969 + 3 ^ 40 * 6090386 * 2
def baseEnd_6090386 : Nat := 3127295389413913570465831

theorem tailTrace_6090386 : CollatzResearch.WordTrace tailWord_6090386 prefixEnd_6090386 3127295389413913570465831 := by
  unfold tailWord_6090386
  simp only [CollatzResearch.WordTrace]
  refine ⟨55533656628394787990732753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148089751009052767975287341 55533656628394787990732753)
  ·
    refine ⟨41650242471296090993049565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55533656628394787990732753 41650242471296090993049565)
    ·
      refine ⟨15618840926736034122393587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41650242471296090993049565 15618840926736034122393587)
      ·
        refine ⟨23428261390104051183590381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15618840926736034122393587 23428261390104051183590381)
        ·
          refine ⟨8785598021289019193846393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23428261390104051183590381 8785598021289019193846393)
          ·
            refine ⟨6589198515966764395384795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8785598021289019193846393 6589198515966764395384795)
            ·
              refine ⟨9883797773950146593077193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6589198515966764395384795 9883797773950146593077193)
              ·
                refine ⟨7412848330462609944807895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9883797773950146593077193 7412848330462609944807895)
                ·
                  refine ⟨11119272495693914917211843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7412848330462609944807895 11119272495693914917211843)
                  ·
                    refine ⟨16678908743540872375817765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11119272495693914917211843 16678908743540872375817765)
                    ·
                      refine ⟨3127295389413913570465831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16678908743540872375817765 3127295389413913570465831)
                      ·
                        rfl

theorem cell23_6090386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_6090386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090386 prefixEnd_6090386 := by exact prefixLift 6090386
  have htrace : WordTrace (prefixWord ++ tailWord_6090386) baseStart_6090386 baseEnd_6090386 := by
    simpa [prefixWord, tailWord_6090386, baseEnd_6090386] using wordTrace_append hprefix tailTrace_6090386
  have hstable : (prefixWord ++ tailWord_6090386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090386).length < 2 ^ (prefixWord ++ tailWord_6090386).sum := by decide
  have hdescent : baseEnd_6090386 < baseStart_6090386 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090399 : List Nat := [1, 1, 2, 7, 1, 1, 1, 2, 1, 2, 4]
def baseStart_6090399 : Nat := 118140960795 + 6090399 * 2 ^ 59
def prefixEnd_6090399 : Nat := 4983230072969 + 3 ^ 40 * 6090399 * 2
def baseEnd_6090399 : Nat := 3127302064662422019603271

theorem tailTrace_6090399 : CollatzResearch.WordTrace tailWord_6090399 prefixEnd_6090399 3127302064662422019603271 := by
  unfold tailWord_6090399
  simp only [CollatzResearch.WordTrace]
  refine ⟨222135100662532055183154251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148090067108354703455436167 222135100662532055183154251)
  ·
    refine ⟨333202650993798082774731377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222135100662532055183154251 333202650993798082774731377)
    ·
      refine ⟨249901988245348562081048533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333202650993798082774731377 249901988245348562081048533)
      ·
        refine ⟨5857077849500356923774575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 249901988245348562081048533 5857077849500356923774575)
        ·
          refine ⟨8785616774250535385661863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5857077849500356923774575 8785616774250535385661863)
          ·
            refine ⟨13178425161375803078492795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8785616774250535385661863 13178425161375803078492795)
            ·
              refine ⟨19767637742063704617739193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13178425161375803078492795 19767637742063704617739193)
              ·
                refine ⟨14825728306547778463304395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19767637742063704617739193 14825728306547778463304395)
                ·
                  refine ⟨22238592459821667694956593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14825728306547778463304395 22238592459821667694956593)
                  ·
                    refine ⟨16678944344866250771217445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22238592459821667694956593 16678944344866250771217445)
                    ·
                      refine ⟨3127302064662422019603271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16678944344866250771217445 3127302064662422019603271)
                      ·
                        rfl

theorem cell23_6090399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_6090399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090399 prefixEnd_6090399 := by exact prefixLift 6090399
  have htrace : WordTrace (prefixWord ++ tailWord_6090399) baseStart_6090399 baseEnd_6090399 := by
    simpa [prefixWord, tailWord_6090399, baseEnd_6090399] using wordTrace_append hprefix tailTrace_6090399
  have hstable : (prefixWord ++ tailWord_6090399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090399).length < 2 ^ (prefixWord ++ tailWord_6090399).sum := by decide
  have hdescent : baseEnd_6090399 < baseStart_6090399 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090419 : List Nat := [1, 1, 1, 2, 3, 3, 4, 2, 2, 1, 3]
def baseStart_6090419 : Nat := 118140960795 + 6090419 * 2 ^ 59
def prefixEnd_6090419 : Nat := 4983230072969 + 3 ^ 40 * 6090419 * 2
def baseEnd_6090419 : Nat := 3127312334275511941353179

theorem tailTrace_6090419 : CollatzResearch.WordTrace tailWord_6090419 prefixEnd_6090419 3127312334275511941353179 := by
  unfold tailWord_6090419
  simp only [CollatzResearch.WordTrace]
  refine ⟨222135830122459598598882311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148090553414973065732588207 222135830122459598598882311)
  ·
    refine ⟨333203745183689397898323467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222135830122459598598882311 333203745183689397898323467)
    ·
      refine ⟨499805617775534096847485201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333203745183689397898323467 499805617775534096847485201)
      ·
        refine ⟨374854213331650572635613901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 499805617775534096847485201 374854213331650572635613901)
        ·
          refine ⟨140570329999368964738355213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 374854213331650572635613901 140570329999368964738355213)
          ·
            refine ⟨52713873749763361776883205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140570329999368964738355213 52713873749763361776883205)
            ·
              refine ⟨9883851328080630333165601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52713873749763361776883205 9883851328080630333165601)
              ·
                refine ⟨7412888496060472749874201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9883851328080630333165601 7412888496060472749874201)
                ·
                  refine ⟨5559666372045354562405651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7412888496060472749874201 5559666372045354562405651)
                  ·
                    refine ⟨8339499558068031843608477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5559666372045354562405651 8339499558068031843608477)
                    ·
                      refine ⟨3127312334275511941353179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8339499558068031843608477 3127312334275511941353179)
                      ·
                        rfl

theorem cell23_6090419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 2, 1, 3].length) (baseStart_6090419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090419 prefixEnd_6090419 := by exact prefixLift 6090419
  have htrace : WordTrace (prefixWord ++ tailWord_6090419) baseStart_6090419 baseEnd_6090419 := by
    simpa [prefixWord, tailWord_6090419, baseEnd_6090419] using wordTrace_append hprefix tailTrace_6090419
  have hstable : (prefixWord ++ tailWord_6090419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090419).length < 2 ^ (prefixWord ++ tailWord_6090419).sum := by decide
  have hdescent : baseEnd_6090419 < baseStart_6090419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090425 : List Nat := [1, 2, 1, 4, 1, 1, 3, 1, 2, 3, 4]
def baseStart_6090425 : Nat := 118140960795 + 6090425 * 2 ^ 59
def prefixEnd_6090425 : Nat := 4983230072969 + 3 ^ 40 * 6090425 * 2
def baseEnd_6090425 : Nat := 3127315415159438917878151

theorem tailTrace_6090425 : CollatzResearch.WordTrace tailWord_6090425 prefixEnd_6090425 3127315415159438917878151 := by
  unfold tailWord_6090425
  simp only [CollatzResearch.WordTrace]
  refine ⟨222136048960437861623600729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148090699306958574415733819 222136048960437861623600729)
  ·
    refine ⟨166602036720328396217700547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222136048960437861623600729 166602036720328396217700547)
    ·
      refine ⟨249903055080492594326550821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166602036720328396217700547 249903055080492594326550821)
      ·
        refine ⟨46856822827592361436228279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 249903055080492594326550821 46856822827592361436228279)
        ·
          refine ⟨70285234241388542154342419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46856822827592361436228279 70285234241388542154342419)
          ·
            refine ⟨105427851362082813231513629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70285234241388542154342419 105427851362082813231513629)
            ·
              refine ⟨39535444260781054961817611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105427851362082813231513629 39535444260781054961817611)
              ·
                refine ⟨59303166391171582442726417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39535444260781054961817611 59303166391171582442726417)
                ·
                  refine ⟨44477374793378686832044813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59303166391171582442726417 44477374793378686832044813)
                  ·
                    refine ⟨16679015547517007562016805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44477374793378686832044813 16679015547517007562016805)
                    ·
                      refine ⟨3127315415159438917878151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16679015547517007562016805 3127315415159438917878151)
                      ·
                        rfl

theorem cell23_6090425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_6090425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090425 prefixEnd_6090425 := by exact prefixLift 6090425
  have htrace : WordTrace (prefixWord ++ tailWord_6090425) baseStart_6090425 baseEnd_6090425 := by
    simpa [prefixWord, tailWord_6090425, baseEnd_6090425] using wordTrace_append hprefix tailTrace_6090425
  have hstable : (prefixWord ++ tailWord_6090425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090425).length < 2 ^ (prefixWord ++ tailWord_6090425).sum := by decide
  have hdescent : baseEnd_6090425 < baseStart_6090425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090455 : List Nat := [1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 4]
def baseStart_6090455 : Nat := 118140960795 + 6090455 * 2 ^ 59
def prefixEnd_6090455 : Nat := 4983230072969 + 3 ^ 40 * 6090455 * 2
def baseEnd_6090455 : Nat := 3127330819579073800503013

theorem tailTrace_6090455 : CollatzResearch.WordTrace tailWord_6090455 prefixEnd_6090455 3127330819579073800503013 := by
  unfold tailWord_6090455
  simp only [CollatzResearch.WordTrace]
  refine ⟨222137143150329176747192819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148091428766886117831461879 222137143150329176747192819)
  ·
    refine ⟨333205714725493765120789229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222137143150329176747192819 333205714725493765120789229)
    ·
      refine ⟨124952143022060161920295961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 333205714725493765120789229 124952143022060161920295961)
      ·
        refine ⟨93714107266545121440221971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124952143022060161920295961 93714107266545121440221971)
        ·
          refine ⟨140571160899817682160332957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93714107266545121440221971 140571160899817682160332957)
          ·
            refine ⟨52714185337431630810124859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140571160899817682160332957 52714185337431630810124859)
            ·
              refine ⟨79071278006147446215187289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52714185337431630810124859 79071278006147446215187289)
              ·
                refine ⟨59303458504610584661390467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79071278006147446215187289 59303458504610584661390467)
                ·
                  refine ⟨88955187756915876992085701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59303458504610584661390467 88955187756915876992085701)
                  ·
                    refine ⟨16679097704421726936016069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 88955187756915876992085701 16679097704421726936016069)
                    ·
                      refine ⟨3127330819579073800503013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16679097704421726936016069 3127330819579073800503013)
                      ·
                        rfl

theorem cell23_6090455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_6090455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090455 prefixEnd_6090455 := by exact prefixLift 6090455
  have htrace : WordTrace (prefixWord ++ tailWord_6090455) baseStart_6090455 baseEnd_6090455 := by
    simpa [prefixWord, tailWord_6090455, baseEnd_6090455] using wordTrace_append hprefix tailTrace_6090455
  have hstable : (prefixWord ++ tailWord_6090455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090455).length < 2 ^ (prefixWord ++ tailWord_6090455).sum := by decide
  have hdescent : baseEnd_6090455 < baseStart_6090455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090472 : List Nat := [2, 1, 4, 1, 3, 1, 1, 2, 2, 2, 4]
def baseStart_6090472 : Nat := 118140960795 + 6090472 * 2 ^ 59
def prefixEnd_6090472 : Nat := 4983230072969 + 3 ^ 40 * 6090472 * 2
def baseEnd_6090472 : Nat := 3127339548750200233990435

theorem tailTrace_6090472 : CollatzResearch.WordTrace tailWord_6090472 prefixEnd_6090472 3127339548750200233990435 := by
  unfold tailWord_6090472
  simp only [CollatzResearch.WordTrace]
  refine ⟨111068881595633794325280835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148091842127511725767041113 111068881595633794325280835)
  ·
    refine ⟨166603322393450691487921253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111068881595633794325280835 166603322393450691487921253)
    ·
      refine ⟨31238122948772004653985235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166603322393450691487921253 31238122948772004653985235)
      ·
        refine ⟨46857184423158006980977853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31238122948772004653985235 46857184423158006980977853)
        ·
          refine ⟨17571444158684252617866695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46857184423158006980977853 17571444158684252617866695)
          ·
            refine ⟨26357166238026378926800043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17571444158684252617866695 26357166238026378926800043)
            ·
              refine ⟨39535749357039568390200065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26357166238026378926800043 39535749357039568390200065)
              ·
                refine ⟨29651812017779676292650049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39535749357039568390200065 29651812017779676292650049)
                ·
                  refine ⟨22238859013334757219487537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29651812017779676292650049 22238859013334757219487537)
                  ·
                    refine ⟨16679144260001067914615653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22238859013334757219487537 16679144260001067914615653)
                    ·
                      refine ⟨3127339548750200233990435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16679144260001067914615653 3127339548750200233990435)
                      ·
                        rfl

theorem cell23_6090472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_6090472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090472 prefixEnd_6090472 := by exact prefixLift 6090472
  have htrace : WordTrace (prefixWord ++ tailWord_6090472) baseStart_6090472 baseEnd_6090472 := by
    simpa [prefixWord, tailWord_6090472, baseEnd_6090472] using wordTrace_append hprefix tailTrace_6090472
  have hstable : (prefixWord ++ tailWord_6090472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090472).length < 2 ^ (prefixWord ++ tailWord_6090472).sum := by decide
  have hdescent : baseEnd_6090472 < baseStart_6090472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090476 : List Nat := [2, 2, 1, 1, 2, 2, 5, 2, 2, 2, 2]
def baseStart_6090476 : Nat := 118140960795 + 6090476 * 2 ^ 59
def prefixEnd_6090476 : Nat := 4983230072969 + 3 ^ 40 * 6090476 * 2
def baseEnd_6090476 : Nat := 3127341602672818218340417

theorem tailTrace_6090476 : CollatzResearch.WordTrace tailWord_6090476 prefixEnd_6090476 3127341602672818218340417 := by
  unfold tailWord_6090476
  simp only [CollatzResearch.WordTrace]
  refine ⟨111068954541626548666853641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148091939388835398222471521 111068954541626548666853641)
  ·
    refine ⟨83301715906219911500140231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111068954541626548666853641 83301715906219911500140231)
    ·
      refine ⟨124952573859329867250210347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83301715906219911500140231 124952573859329867250210347)
      ·
        refine ⟨187428860788994800875315521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124952573859329867250210347 187428860788994800875315521)
        ·
          refine ⟨140571645591746100656486641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187428860788994800875315521 140571645591746100656486641)
          ·
            refine ⟨105428734193809575492364981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140571645591746100656486641 105428734193809575492364981)
            ·
              refine ⟨9883943830669647702409217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 105428734193809575492364981 9883943830669647702409217)
              ·
                refine ⟨7412957873002235776806913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9883943830669647702409217 7412957873002235776806913)
                ·
                  refine ⟨5559718404751676832605185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7412957873002235776806913 5559718404751676832605185)
                  ·
                    refine ⟨4169788803563757624453889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5559718404751676832605185 4169788803563757624453889)
                    ·
                      refine ⟨3127341602672818218340417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4169788803563757624453889 3127341602672818218340417)
                      ·
                        rfl

theorem cell23_6090476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 2, 2].length) (baseStart_6090476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090476 prefixEnd_6090476 := by exact prefixLift 6090476
  have htrace : WordTrace (prefixWord ++ tailWord_6090476) baseStart_6090476 baseEnd_6090476 := by
    simpa [prefixWord, tailWord_6090476, baseEnd_6090476] using wordTrace_append hprefix tailTrace_6090476
  have hstable : (prefixWord ++ tailWord_6090476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090476).length < 2 ^ (prefixWord ++ tailWord_6090476).sum := by decide
  have hdescent : baseEnd_6090476 < baseStart_6090476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090482 : List Nat := [3, 2, 1, 3, 1, 1, 4, 1, 7]
def baseStart_6090482 : Nat := 118140960795 + 6090482 * 2 ^ 59
def prefixEnd_6090482 : Nat := 4983230072969 + 3 ^ 40 * 6090482 * 2
def baseEnd_6090482 : Nat := 347482742617416132762821

theorem tailTrace_6090482 : CollatzResearch.WordTrace tailWord_6090482 prefixEnd_6090482 347482742617416132762821 := by
  unfold tailWord_6090482
  simp only [CollatzResearch.WordTrace]
  refine ⟨55534531980307840089606425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148092085280820906905617133 55534531980307840089606425)
  ·
    refine ⟨41650898985230880067204819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55534531980307840089606425 41650898985230880067204819)
    ·
      refine ⟨62476348477846320100807229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41650898985230880067204819 62476348477846320100807229)
      ·
        refine ⟨23428630679192370037802711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62476348477846320100807229 23428630679192370037802711)
        ·
          refine ⟨35142946018788555056704067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23428630679192370037802711 35142946018788555056704067)
          ·
            refine ⟨52714419028182832585056101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35142946018788555056704067 52714419028182832585056101)
            ·
              refine ⟨9883953567784281109698019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52714419028182832585056101 9883953567784281109698019)
              ·
                refine ⟨14825930351676421664547029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9883953567784281109698019 14825930351676421664547029)
                ·
                  refine ⟨347482742617416132762821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14825930351676421664547029 347482742617416132762821)
                  ·
                    rfl

theorem cell23_6090482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 7].length) (baseStart_6090482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090482 prefixEnd_6090482 := by exact prefixLift 6090482
  have htrace : WordTrace (prefixWord ++ tailWord_6090482) baseStart_6090482 baseEnd_6090482 := by
    simpa [prefixWord, tailWord_6090482, baseEnd_6090482] using wordTrace_append hprefix tailTrace_6090482
  have hstable : (prefixWord ++ tailWord_6090482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090482).length < 2 ^ (prefixWord ++ tailWord_6090482).sum := by decide
  have hdescent : baseEnd_6090482 < baseStart_6090482 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090492 : List Nat := [2, 2, 2, 1, 3, 1, 1, 3, 2, 3, 3]
def baseStart_6090492 : Nat := 118140960795 + 6090492 * 2 ^ 59
def prefixEnd_6090492 : Nat := 4983230072969 + 3 ^ 40 * 6090492 * 2
def baseEnd_6090492 : Nat := 3127349818363290155740343

theorem tailTrace_6090492 : CollatzResearch.WordTrace tailWord_6090492 prefixEnd_6090492 3127349818363290155740343 := by
  unfold tailWord_6090492
  simp only [CollatzResearch.WordTrace]
  refine ⟨111069246325597566033144865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148092328434130088044193153 111069246325597566033144865)
  ·
    refine ⟨83301934744198174524858649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111069246325597566033144865 83301934744198174524858649)
    ·
      refine ⟨62476451058148630893643987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83301934744198174524858649 62476451058148630893643987)
      ·
        refine ⟨93714676587222946340465981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62476451058148630893643987 93714676587222946340465981)
        ·
          refine ⟨35143003720208604877674743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93714676587222946340465981 35143003720208604877674743)
          ·
            refine ⟨52714505580312907316512115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35143003720208604877674743 52714505580312907316512115)
            ·
              refine ⟨79071758370469360974768173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52714505580312907316512115 79071758370469360974768173)
              ·
                refine ⟨29651909388926010365538065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79071758370469360974768173 29651909388926010365538065)
                ·
                  refine ⟨22238932041694507774153549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29651909388926010365538065 22238932041694507774153549)
                  ·
                    refine ⟨8339599515635440415307581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22238932041694507774153549 8339599515635440415307581)
                    ·
                      refine ⟨3127349818363290155740343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8339599515635440415307581 3127349818363290155740343)
                      ·
                        rfl

theorem cell23_6090492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 3, 2, 3, 3].length) (baseStart_6090492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090492 prefixEnd_6090492 := by exact prefixLift 6090492
  have htrace : WordTrace (prefixWord ++ tailWord_6090492) baseStart_6090492 baseEnd_6090492 := by
    simpa [prefixWord, tailWord_6090492, baseEnd_6090492] using wordTrace_append hprefix tailTrace_6090492
  have hstable : (prefixWord ++ tailWord_6090492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090492).length < 2 ^ (prefixWord ++ tailWord_6090492).sum := by decide
  have hdescent : baseEnd_6090492 < baseStart_6090492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090495 : List Nat := [1, 1, 2, 2, 1, 3, 3, 2, 1, 7]
def baseStart_6090495 : Nat := 118140960795 + 6090495 * 2 ^ 59
def prefixEnd_6090495 : Nat := 4983230072969 + 3 ^ 40 * 6090495 * 2
def baseEnd_6090495 : Nat := 1042450452935084548000943

theorem tailTrace_6090495 : CollatzResearch.WordTrace tailWord_6090495 prefixEnd_6090495 1042450452935084548000943 := by
  unfold tailWord_6090495
  simp only [CollatzResearch.WordTrace]
  refine ⟨222138602070184263578648939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148092401380122842385765959 222138602070184263578648939)
  ·
    refine ⟨333207903105276395367973409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222138602070184263578648939 333207903105276395367973409)
    ·
      refine ⟨249905927328957296525980057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333207903105276395367973409 249905927328957296525980057)
      ·
        refine ⟨187429445496717972394485043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249905927328957296525980057 187429445496717972394485043)
        ·
          refine ⟨281144168245076958591727565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187429445496717972394485043 281144168245076958591727565)
          ·
            refine ⟨105429063091903859471897837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 281144168245076958591727565 105429063091903859471897837)
            ·
              refine ⟨39535898659463947301961689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105429063091903859471897837 39535898659463947301961689)
              ·
                refine ⟨29651923994597960476471267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39535898659463947301961689 29651923994597960476471267)
                ·
                  refine ⟨44477885991896940714706901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29651923994597960476471267 44477885991896940714706901)
                  ·
                    refine ⟨1042450452935084548000943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44477885991896940714706901 1042450452935084548000943)
                    ·
                      rfl

theorem cell23_6090495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 7].length) (baseStart_6090495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090495 prefixEnd_6090495 := by exact prefixLift 6090495
  have htrace : WordTrace (prefixWord ++ tailWord_6090495) baseStart_6090495 baseEnd_6090495 := by
    simpa [prefixWord, tailWord_6090495, baseEnd_6090495] using wordTrace_append hprefix tailTrace_6090495
  have hstable : (prefixWord ++ tailWord_6090495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090495).length < 2 ^ (prefixWord ++ tailWord_6090495).sum := by decide
  have hdescent : baseEnd_6090495 < baseStart_6090495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090505 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 3, 2, 5]
def baseStart_6090505 : Nat := 118140960795 + 6090505 * 2 ^ 59
def prefixEnd_6090505 : Nat := 4983230072969 + 3 ^ 40 * 6090505 * 2
def baseEnd_6090505 : Nat := 3127356493611798604877783

theorem tailTrace_6090505 : CollatzResearch.WordTrace tailWord_6090505 prefixEnd_6090505 3127356493611798604877783 := by
  unfold tailWord_6090505
  simp only [CollatzResearch.WordTrace]
  refine ⟨222138966800148035286512969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148092644533432023524341979 222138966800148035286512969)
  ·
    refine ⟨166604225100111026464884727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222138966800148035286512969 166604225100111026464884727)
    ·
      refine ⟨249906337650166539697327091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166604225100111026464884727 249906337650166539697327091)
      ·
        refine ⟨374859506475249809545990637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249906337650166539697327091 374859506475249809545990637)
        ·
          refine ⟨140572314928218678579746489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 374859506475249809545990637 140572314928218678579746489)
          ·
            refine ⟨105429236196164008934809867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140572314928218678579746489 105429236196164008934809867)
            ·
              refine ⟨158143854294246013402214801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105429236196164008934809867 158143854294246013402214801)
              ·
                refine ⟨118607890720684510051661101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158143854294246013402214801 118607890720684510051661101)
                ·
                  refine ⟨44477959020256691269372913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118607890720684510051661101 44477959020256691269372913)
                  ·
                    refine ⟨33358469265192518452029685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44477959020256691269372913 33358469265192518452029685)
                    ·
                      refine ⟨3127356493611798604877783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33358469265192518452029685 3127356493611798604877783)
                      ·
                        rfl

theorem cell23_6090505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 2, 5].length) (baseStart_6090505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090505 prefixEnd_6090505 := by exact prefixLift 6090505
  have htrace : WordTrace (prefixWord ++ tailWord_6090505) baseStart_6090505 baseEnd_6090505 := by
    simpa [prefixWord, tailWord_6090505, baseEnd_6090505] using wordTrace_append hprefix tailTrace_6090505
  have hstable : (prefixWord ++ tailWord_6090505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090505).length < 2 ^ (prefixWord ++ tailWord_6090505).sum := by decide
  have hdescent : baseEnd_6090505 < baseStart_6090505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090569 : List Nat := [1, 2, 1, 1, 2, 4, 4, 1, 2, 2, 3]
def baseStart_6090569 : Nat := 118140960795 + 6090569 * 2 ^ 59
def prefixEnd_6090569 : Nat := 4983230072969 + 3 ^ 40 * 6090569 * 2
def baseEnd_6090569 : Nat := 3127389356373686354477489

theorem tailTrace_6090569 : CollatzResearch.WordTrace tailWord_6090569 prefixEnd_6090569 3127389356373686354477489 := by
  unfold tailWord_6090569
  simp only [CollatzResearch.WordTrace]
  refine ⟨222141301071916174216842761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148094200714610782811228507 222141301071916174216842761)
  ·
    refine ⟨166605975803937130662632071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222141301071916174216842761 166605975803937130662632071)
    ·
      refine ⟨249908963705905695993948107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166605975803937130662632071 249908963705905695993948107)
      ·
        refine ⟨374863445558858543990922161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249908963705905695993948107 374863445558858543990922161)
        ·
          refine ⟨281147584169143907993191621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374863445558858543990922161 281147584169143907993191621)
          ·
            refine ⟨52715172031714482748723429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 281147584169143907993191621 52715172031714482748723429)
            ·
              refine ⟨9884094755946465515385643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52715172031714482748723429 9884094755946465515385643)
              ·
                refine ⟨14826142133919698273078465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9884094755946465515385643 14826142133919698273078465)
                ·
                  refine ⟨11119606600439773704808849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14826142133919698273078465 11119606600439773704808849)
                  ·
                    refine ⟨8339704950329830278606637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11119606600439773704808849 8339704950329830278606637)
                    ·
                      refine ⟨3127389356373686354477489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8339704950329830278606637 3127389356373686354477489)
                      ·
                        rfl

theorem cell23_6090569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 2, 3].length) (baseStart_6090569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090569 prefixEnd_6090569 := by exact prefixLift 6090569
  have htrace : WordTrace (prefixWord ++ tailWord_6090569) baseStart_6090569 baseEnd_6090569 := by
    simpa [prefixWord, tailWord_6090569, baseEnd_6090569] using wordTrace_append hprefix tailTrace_6090569
  have hstable : (prefixWord ++ tailWord_6090569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090569).length < 2 ^ (prefixWord ++ tailWord_6090569).sum := by decide
  have hdescent : baseEnd_6090569 < baseStart_6090569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090609 : List Nat := [1, 2, 2, 2, 1, 3, 2, 2, 1, 5, 2]
def baseStart_6090609 : Nat := 118140960795 + 6090609 * 2 ^ 59
def prefixEnd_6090609 : Nat := 4983230072969 + 3 ^ 40 * 6090609 * 2
def baseEnd_6090609 : Nat := 3127409895599866197977305

theorem tailTrace_6090609 : CollatzResearch.WordTrace tailWord_6090609 prefixEnd_6090609 3127409895599866197977305 := by
  unfold tailWord_6090609
  simp only [CollatzResearch.WordTrace]
  refine ⟨222142759991771261048298881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148095173327847507365532587 222142759991771261048298881)
  ·
    refine ⟨166607069993828445786224161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222142759991771261048298881 166607069993828445786224161)
    ·
      refine ⟨124955302495371334339668121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166607069993828445786224161 124955302495371334339668121)
      ·
        refine ⟨93716476871528500754751091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124955302495371334339668121 93716476871528500754751091)
        ·
          refine ⟨140574715307292751132126637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93716476871528500754751091 140574715307292751132126637)
          ·
            refine ⟨52715518240234781674547489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140574715307292751132126637 52715518240234781674547489)
            ·
              refine ⟨39536638680176086255910617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52715518240234781674547489 39536638680176086255910617)
              ·
                refine ⟨29652479010132064691932963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39536638680176086255910617 29652479010132064691932963)
                ·
                  refine ⟨44478718515198097037899445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29652479010132064691932963 44478718515198097037899445)
                  ·
                    refine ⟨4169879860799821597303073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44478718515198097037899445 4169879860799821597303073)
                    ·
                      refine ⟨3127409895599866197977305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4169879860799821597303073 3127409895599866197977305)
                      ·
                        rfl

theorem cell23_6090609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 5, 2].length) (baseStart_6090609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090609 prefixEnd_6090609 := by exact prefixLift 6090609
  have htrace : WordTrace (prefixWord ++ tailWord_6090609) baseStart_6090609 baseEnd_6090609 := by
    simpa [prefixWord, tailWord_6090609, baseEnd_6090609] using wordTrace_append hprefix tailTrace_6090609
  have hstable : (prefixWord ++ tailWord_6090609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090609).length < 2 ^ (prefixWord ++ tailWord_6090609).sum := by decide
  have hdescent : baseEnd_6090609 < baseStart_6090609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090633 : List Nat := [1, 2, 1, 1, 5, 1, 4, 3, 1, 1, 3]
def baseStart_6090633 : Nat := 118140960795 + 6090633 * 2 ^ 59
def prefixEnd_6090633 : Nat := 4983230072969 + 3 ^ 40 * 6090633 * 2
def baseEnd_6090633 : Nat := 3127422219135574104077195

theorem tailTrace_6090633 : CollatzResearch.WordTrace tailWord_6090633 prefixEnd_6090633 3127422219135574104077195 := by
  unfold tailWord_6090633
  simp only [CollatzResearch.WordTrace]
  refine ⟨222143635343684313147172553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148095756895789542098115035 222143635343684313147172553)
  ·
    refine ⟨166607726507763234860379415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222143635343684313147172553 166607726507763234860379415)
    ·
      refine ⟨249911589761644852290569123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166607726507763234860379415 249911589761644852290569123)
      ·
        refine ⟨374867384642467278435853685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249911589761644852290569123 374867384642467278435853685)
        ·
          refine ⟨35143817310231307353361283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 374867384642467278435853685 35143817310231307353361283)
          ·
            refine ⟨52715725965346961030041925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35143817310231307353361283 52715725965346961030041925)
            ·
              refine ⟨9884198618502555193132861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52715725965346961030041925 9884198618502555193132861)
              ·
                refine ⟨3706574481938458197424823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9884198618502555193132861 3706574481938458197424823)
                ·
                  refine ⟨5559861722907687296137235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3706574481938458197424823 5559861722907687296137235)
                  ·
                    refine ⟨8339792584361530944205853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5559861722907687296137235 8339792584361530944205853)
                    ·
                      refine ⟨3127422219135574104077195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8339792584361530944205853 3127422219135574104077195)
                      ·
                        rfl

theorem cell23_6090633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 3, 1, 1, 3].length) (baseStart_6090633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090633 prefixEnd_6090633 := by exact prefixLift 6090633
  have htrace : WordTrace (prefixWord ++ tailWord_6090633) baseStart_6090633 baseEnd_6090633 := by
    simpa [prefixWord, tailWord_6090633, baseEnd_6090633] using wordTrace_append hprefix tailTrace_6090633
  have hstable : (prefixWord ++ tailWord_6090633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090633).length < 2 ^ (prefixWord ++ tailWord_6090633).sum := by decide
  have hdescent : baseEnd_6090633 < baseStart_6090633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090673 : List Nat := [1, 2, 2, 4, 2, 1, 2, 2, 3, 2, 2]
def baseStart_6090673 : Nat := 118140960795 + 6090673 * 2 ^ 59
def prefixEnd_6090673 : Nat := 4983230072969 + 3 ^ 40 * 6090673 * 2
def baseEnd_6090673 : Nat := 3127442758361753947577011

theorem tailTrace_6090673 : CollatzResearch.WordTrace tailWord_6090673 prefixEnd_6090673 3127442758361753947577011 := by
  unfold tailWord_6090673
  simp only [CollatzResearch.WordTrace]
  refine ⟨222145094263539399978628673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148096729509026266652419115 222145094263539399978628673)
  ·
    refine ⟨166608820697654549983971505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222145094263539399978628673 166608820697654549983971505)
    ·
      refine ⟨124956615523240912487978629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166608820697654549983971505 124956615523240912487978629)
      ·
        refine ⟨23429365410607671091495993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124956615523240912487978629 23429365410607671091495993)
        ·
          refine ⟨17572024057955753318621995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23429365410607671091495993 17572024057955753318621995)
          ·
            refine ⟨26358036086933629977932993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17572024057955753318621995 26358036086933629977932993)
            ·
              refine ⟨19768527065200222483449745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26358036086933629977932993 19768527065200222483449745)
              ·
                refine ⟨14826395298900166862587309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19768527065200222483449745 14826395298900166862587309)
                ·
                  refine ⟨5559898237087562573470241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14826395298900166862587309 5559898237087562573470241)
                  ·
                    refine ⟨4169923677815671930102681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5559898237087562573470241 4169923677815671930102681)
                    ·
                      refine ⟨3127442758361753947577011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4169923677815671930102681 3127442758361753947577011)
                      ·
                        rfl

theorem cell23_6090673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_6090673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090673 prefixEnd_6090673 := by exact prefixLift 6090673
  have htrace : WordTrace (prefixWord ++ tailWord_6090673) baseStart_6090673 baseEnd_6090673 := by
    simpa [prefixWord, tailWord_6090673, baseEnd_6090673] using wordTrace_append hprefix tailTrace_6090673
  have hstable : (prefixWord ++ tailWord_6090673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090673).length < 2 ^ (prefixWord ++ tailWord_6090673).sum := by decide
  have hdescent : baseEnd_6090673 < baseStart_6090673 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090684 : List Nat := [2, 2, 2, 5, 2, 1, 1, 3, 1, 1, 3]
def baseStart_6090684 : Nat := 118140960795 + 6090684 * 2 ^ 59
def prefixEnd_6090684 : Nat := 4983230072969 + 3 ^ 40 * 6090684 * 2
def baseEnd_6090684 : Nat := 3127448406648953404539461

theorem tailTrace_6090684 : CollatzResearch.WordTrace tailWord_6090684 prefixEnd_6090684 3127448406648953404539461 := by
  unfold tailWord_6090684
  simp only [CollatzResearch.WordTrace]
  refine ⟨111072747733249774428639553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148096996977666365904852737 111072747733249774428639553)
  ·
    refine ⟨83304560799937330821479665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111072747733249774428639553 83304560799937330821479665)
    ·
      refine ⟨62478420599952998116109749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83304560799937330821479665 62478420599952998116109749)
      ·
        refine ⟨5857351931245593573385289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62478420599952998116109749 5857351931245593573385289)
        ·
          refine ⟨4393013948434195180038967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5857351931245593573385289 4393013948434195180038967)
          ·
            refine ⟨6589520922651292770058451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4393013948434195180038967 6589520922651292770058451)
            ·
              refine ⟨9884281383976939155087677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6589520922651292770058451 9884281383976939155087677)
              ·
                refine ⟨3706605518991352183157879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9884281383976939155087677 3706605518991352183157879)
                ·
                  refine ⟨5559908278487028274736819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3706605518991352183157879 5559908278487028274736819)
                  ·
                    refine ⟨8339862417730542412105229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5559908278487028274736819 8339862417730542412105229)
                    ·
                      refine ⟨3127448406648953404539461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8339862417730542412105229 3127448406648953404539461)
                      ·
                        rfl

theorem cell23_6090684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_6090684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090684 prefixEnd_6090684 := by exact prefixLift 6090684
  have htrace : WordTrace (prefixWord ++ tailWord_6090684) baseStart_6090684 baseEnd_6090684 := by
    simpa [prefixWord, tailWord_6090684, baseEnd_6090684] using wordTrace_append hprefix tailTrace_6090684
  have hstable : (prefixWord ++ tailWord_6090684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090684).length < 2 ^ (prefixWord ++ tailWord_6090684).sum := by decide
  have hdescent : baseEnd_6090684 < baseStart_6090684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090717 : List Nat := [1, 4, 3, 1, 4, 1, 2, 1, 2, 4]
def baseStart_6090717 : Nat := 118140960795 + 6090717 * 2 ^ 59
def prefixEnd_6090717 : Nat := 4983230072969 + 3 ^ 40 * 6090717 * 2
def baseEnd_6090717 : Nat := 1042488450503517258475603

theorem tailTrace_6090717 : CollatzResearch.WordTrace tailWord_6090717 prefixEnd_6090717 1042488450503517258475603 := by
  unfold tailWord_6090717
  simp only [CollatzResearch.WordTrace]
  refine ⟨222146699075379995493230405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148097799383586663662153603 222146699075379995493230405)
  ·
    refine ⟨41652506076633749154980701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222146699075379995493230405 41652506076633749154980701)
    ·
      refine ⟨15619689778737655933117763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41652506076633749154980701 15619689778737655933117763)
      ·
        refine ⟨23429534668106483899676645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15619689778737655933117763 23429534668106483899676645)
        ·
          refine ⟨4393037750269965731189371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23429534668106483899676645 4393037750269965731189371)
          ·
            refine ⟨6589556625404948596784057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4393037750269965731189371 6589556625404948596784057)
            ·
              refine ⟨4942167469053711447588043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6589556625404948596784057 4942167469053711447588043)
              ·
                refine ⟨7413251203580567171382065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4942167469053711447588043 7413251203580567171382065)
                ·
                  refine ⟨5559938402685425378536549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7413251203580567171382065 5559938402685425378536549)
                  ·
                    refine ⟨1042488450503517258475603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5559938402685425378536549 1042488450503517258475603)
                    ·
                      rfl

theorem cell23_6090717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_6090717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090717 prefixEnd_6090717 := by exact prefixLift 6090717
  have htrace : WordTrace (prefixWord ++ tailWord_6090717) baseStart_6090717 baseEnd_6090717 := by
    simpa [prefixWord, tailWord_6090717, baseEnd_6090717] using wordTrace_append hprefix tailTrace_6090717
  have hstable : (prefixWord ++ tailWord_6090717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090717).length < 2 ^ (prefixWord ++ tailWord_6090717).sum := by decide
  have hdescent : baseEnd_6090717 < baseStart_6090717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090723 : List Nat := [1, 1, 1, 6, 1, 3, 1, 3, 2, 1, 3]
def baseStart_6090723 : Nat := 118140960795 + 6090723 * 2 ^ 59
def prefixEnd_6090723 : Nat := 4983230072969 + 3 ^ 40 * 6090723 * 2
def baseEnd_6090723 : Nat := 3127468432394478751951781

theorem tailTrace_6090723 : CollatzResearch.WordTrace tailWord_6090723 prefixEnd_6090723 3127468432394478751951781 := by
  unfold tailWord_6090723
  simp only [CollatzResearch.WordTrace]
  refine ⟨222146917913358258517948823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148097945275572172345299215 222146917913358258517948823)
  ·
    refine ⟨333220376870037387776923235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222146917913358258517948823 333220376870037387776923235)
    ·
      refine ⟨499830565305056081665384853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333220376870037387776923235 499830565305056081665384853)
      ·
        refine ⟨23429557748674503828064915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 499830565305056081665384853 23429557748674503828064915)
        ·
          refine ⟨35144336623011755742097373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23429557748674503828064915 35144336623011755742097373)
          ·
            refine ⟨13179126233629408403286515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35144336623011755742097373 13179126233629408403286515)
            ·
              refine ⟨19768689350444112604929773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13179126233629408403286515 19768689350444112604929773)
              ·
                refine ⟨7413258506416542226848665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19768689350444112604929773 7413258506416542226848665)
                ·
                  refine ⟨5559943879812406670136499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7413258506416542226848665 5559943879812406670136499)
                  ·
                    refine ⟨8339915819718610005204749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5559943879812406670136499 8339915819718610005204749)
                    ·
                      refine ⟨3127468432394478751951781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8339915819718610005204749 3127468432394478751951781)
                      ·
                        rfl

theorem cell23_6090723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_6090723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090723 prefixEnd_6090723 := by exact prefixLift 6090723
  have htrace : WordTrace (prefixWord ++ tailWord_6090723) baseStart_6090723 baseEnd_6090723 := by
    simpa [prefixWord, tailWord_6090723, baseEnd_6090723] using wordTrace_append hprefix tailTrace_6090723
  have hstable : (prefixWord ++ tailWord_6090723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090723).length < 2 ^ (prefixWord ++ tailWord_6090723).sum := by decide
  have hdescent : baseEnd_6090723 < baseStart_6090723 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090749 : List Nat := [1, 4, 1, 1, 1, 2, 4, 1, 2, 1, 5]
def baseStart_6090749 : Nat := 118140960795 + 6090749 * 2 ^ 59
def prefixEnd_6090749 : Nat := 4983230072969 + 3 ^ 40 * 6090749 * 2
def baseEnd_6090749 : Nat := 3127481782891495650226661

theorem tailTrace_6090749 : CollatzResearch.WordTrace tailWord_6090749 prefixEnd_6090749 3127481782891495650226661 := by
  unfold tailWord_6090749
  simp only [CollatzResearch.WordTrace]
  refine ⟨222147866211264064958395301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148098577474176043305596867 222147866211264064958395301)
  ·
    refine ⟨41652724914612012179699119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222147866211264064958395301 41652724914612012179699119)
    ·
      refine ⟨62479087371918018269548679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41652724914612012179699119 62479087371918018269548679)
      ·
        refine ⟨93718631057877027404323019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62479087371918018269548679 93718631057877027404323019)
        ·
          refine ⟨140577946586815541106484529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93718631057877027404323019 140577946586815541106484529)
          ·
            refine ⟨105433459940111655829863397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140577946586815541106484529 105433459940111655829863397)
            ·
              refine ⟨19768773738770935468099387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105433459940111655829863397 19768773738770935468099387)
              ·
                refine ⟨29653160608156403202149081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19768773738770935468099387 29653160608156403202149081)
                ·
                  refine ⟨22239870456117302401611811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29653160608156403202149081 22239870456117302401611811)
                  ·
                    refine ⟨33359805684175953602417717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22239870456117302401611811 33359805684175953602417717)
                    ·
                      refine ⟨3127481782891495650226661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33359805684175953602417717 3127481782891495650226661)
                      ·
                        rfl

theorem cell23_6090749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_6090749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090749 prefixEnd_6090749 := by exact prefixLift 6090749
  have htrace : WordTrace (prefixWord ++ tailWord_6090749) baseStart_6090749 baseEnd_6090749 := by
    simpa [prefixWord, tailWord_6090749, baseEnd_6090749] using wordTrace_append hprefix tailTrace_6090749
  have hstable : (prefixWord ++ tailWord_6090749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090749).length < 2 ^ (prefixWord ++ tailWord_6090749).sum := by decide
  have hdescent : baseEnd_6090749 < baseStart_6090749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090752 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 11]
def baseStart_6090752 : Nat := 118140960795 + 6090752 * 2 ^ 59
def prefixEnd_6090752 : Nat := 4983230072969 + 3 ^ 40 * 6090752 * 2
def baseEnd_6090752 : Nat := 347498147037051015387683

theorem tailTrace_6090752 : CollatzResearch.WordTrace tailWord_6090752 prefixEnd_6090752 347498147037051015387683 := by
  unfold tailWord_6090752
  simp only [CollatzResearch.WordTrace]
  refine ⟨111073987815126598235377255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148098650420168797647169673 111073987815126598235377255)
  ·
    refine ⟨166610981722689897353065883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111073987815126598235377255 166610981722689897353065883)
    ·
      refine ⟨249916472584034846029598825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166610981722689897353065883 249916472584034846029598825)
      ·
        refine ⟨187437354438026134522199119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 249916472584034846029598825 187437354438026134522199119)
        ·
          refine ⟨281156031657039201783298679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187437354438026134522199119 281156031657039201783298679)
          ·
            refine ⟨421734047485558802674948019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281156031657039201783298679 421734047485558802674948019)
            ·
              refine ⟨632601071228338204012422029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 421734047485558802674948019 632601071228338204012422029)
              ·
                refine ⟨237225401710626826504658261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 632601071228338204012422029 237225401710626826504658261)
                ·
                  refine ⟨347498147037051015387683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 237225401710626826504658261 347498147037051015387683)
                  ·
                    rfl

theorem cell23_6090752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 11].length) (baseStart_6090752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090752 prefixEnd_6090752 := by exact prefixLift 6090752
  have htrace : WordTrace (prefixWord ++ tailWord_6090752) baseStart_6090752 baseEnd_6090752 := by
    simpa [prefixWord, tailWord_6090752, baseEnd_6090752] using wordTrace_append hprefix tailTrace_6090752
  have hstable : (prefixWord ++ tailWord_6090752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090752).length < 2 ^ (prefixWord ++ tailWord_6090752).sum := by decide
  have hdescent : baseEnd_6090752 < baseStart_6090752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090758 : List Nat := [6, 2, 1, 2, 1, 1, 1, 4, 1, 2, 2]
def baseStart_6090758 : Nat := 118140960795 + 6090758 * 2 ^ 59
def prefixEnd_6090758 : Nat := 4983230072969 + 3 ^ 40 * 6090758 * 2
def baseEnd_6090758 : Nat := 3127486404217386115014121

theorem tailTrace_6090758 : CollatzResearch.WordTrace tailWord_6090758 prefixEnd_6090758 3127486404217386115014121 := by
  unfold tailWord_6090758
  simp only [CollatzResearch.WordTrace]
  refine ⟨6942131077132233109233529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 148098796312154306330315285 6942131077132233109233529)
  ·
    refine ⟨5206598307849174831925147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6942131077132233109233529 5206598307849174831925147)
    ·
      refine ⟨7809897461773762247887721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5206598307849174831925147 7809897461773762247887721)
      ·
        refine ⟨5857423096330321685915791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7809897461773762247887721 5857423096330321685915791)
        ·
          refine ⟨8786134644495482528873687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5857423096330321685915791 8786134644495482528873687)
          ·
            refine ⟨13179201966743223793310531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8786134644495482528873687 13179201966743223793310531)
            ·
              refine ⟨19768802950114835689965797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13179201966743223793310531 19768802950114835689965797)
              ·
                refine ⟨3706650553146531691868587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19768802950114835689965797 3706650553146531691868587)
                ·
                  refine ⟨5559975829719797537802881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3706650553146531691868587 5559975829719797537802881)
                  ·
                    refine ⟨4169981872289848153352161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5559975829719797537802881 4169981872289848153352161)
                    ·
                      refine ⟨3127486404217386115014121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4169981872289848153352161 3127486404217386115014121)
                      ·
                        rfl

theorem cell23_6090758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_6090758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090758 prefixEnd_6090758 := by exact prefixLift 6090758
  have htrace : WordTrace (prefixWord ++ tailWord_6090758) baseStart_6090758 baseEnd_6090758 := by
    simpa [prefixWord, tailWord_6090758, baseEnd_6090758] using wordTrace_append hprefix tailTrace_6090758
  have hstable : (prefixWord ++ tailWord_6090758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090758).length < 2 ^ (prefixWord ++ tailWord_6090758).sum := by decide
  have hdescent : baseEnd_6090758 < baseStart_6090758 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090780 : List Nat := [2, 2, 3, 1, 3, 1, 2, 3, 2, 2, 2]
def baseStart_6090780 : Nat := 118140960795 + 6090780 * 2 ^ 59
def prefixEnd_6090780 : Nat := 4983230072969 + 3 ^ 40 * 6090780 * 2
def baseEnd_6090780 : Nat := 3127497700791785028939019

theorem tailTrace_6090780 : CollatzResearch.WordTrace tailWord_6090780 prefixEnd_6090780 3127497700791785028939019 := by
  unfold tailWord_6090780
  simp only [CollatzResearch.WordTrace]
  refine ⟨111074498437075878626386897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148099331249434504835182529 111074498437075878626386897)
  ·
    refine ⟨83305873827806908969790173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111074498437075878626386897 83305873827806908969790173)
    ·
      refine ⟨31239702685427590863671315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83305873827806908969790173 31239702685427590863671315)
      ·
        refine ⟨46859554028141386295506973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31239702685427590863671315 46859554028141386295506973)
        ·
          refine ⟨17572332760553019860815115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46859554028141386295506973 17572332760553019860815115)
          ·
            refine ⟨26358499140829529791222673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17572332760553019860815115 26358499140829529791222673)
            ·
              refine ⟨19768874355622147343417005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26358499140829529791222673 19768874355622147343417005)
              ·
                refine ⟨7413327883358305253781377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19768874355622147343417005 7413327883358305253781377)
                ·
                  refine ⟨5559995912518728940336033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7413327883358305253781377 5559995912518728940336033)
                  ·
                    refine ⟨4169996934389046705252025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5559995912518728940336033 4169996934389046705252025)
                    ·
                      refine ⟨3127497700791785028939019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4169996934389046705252025 3127497700791785028939019)
                      ·
                        rfl

theorem cell23_6090780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_6090780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090780 prefixEnd_6090780 := by exact prefixLift 6090780
  have htrace : WordTrace (prefixWord ++ tailWord_6090780) baseStart_6090780 baseEnd_6090780 := by
    simpa [prefixWord, tailWord_6090780, baseEnd_6090780] using wordTrace_append hprefix tailTrace_6090780
  have hstable : (prefixWord ++ tailWord_6090780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090780).length < 2 ^ (prefixWord ++ tailWord_6090780).sum := by decide
  have hdescent : baseEnd_6090780 < baseStart_6090780 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090799 : List Nat := [1, 1, 2, 1, 2, 1, 1, 7, 2, 5]
def baseStart_6090799 : Nat := 118140960795 + 6090799 * 2 ^ 59
def prefixEnd_6090799 : Nat := 4983230072969 + 3 ^ 40 * 6090799 * 2
def baseEnd_6090799 : Nat := 1042502485641406818200477

theorem tailTrace_6090799 : CollatzResearch.WordTrace tailWord_6090799 prefixEnd_6090799 1042502485641406818200477 := by
  unfold tailWord_6090799
  simp only [CollatzResearch.WordTrace]
  refine ⟨222149689861082923497715451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148099793240721948998476967 222149689861082923497715451)
  ·
    refine ⟨333224534791624385246573177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222149689861082923497715451 333224534791624385246573177)
    ·
      refine ⟨249918401093718288934929883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333224534791624385246573177 249918401093718288934929883)
      ·
        refine ⟨374877601640577433402394825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249918401093718288934929883 374877601640577433402394825)
        ·
          refine ⟨281158201230433075051796119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374877601640577433402394825 281158201230433075051796119)
          ·
            refine ⟨421737301845649612577694179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281158201230433075051796119 421737301845649612577694179)
            ·
              refine ⟨632605952768474418866541269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 421737301845649612577694179 632605952768474418866541269)
              ·
                refine ⟨14826702018011119192184561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 632605952768474418866541269 14826702018011119192184561)
                ·
                  refine ⟨11120026513508339394138421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14826702018011119192184561 11120026513508339394138421)
                  ·
                    refine ⟨1042502485641406818200477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11120026513508339394138421 1042502485641406818200477)
                    ·
                      rfl

theorem cell23_6090799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 2, 5].length) (baseStart_6090799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090799 prefixEnd_6090799 := by exact prefixLift 6090799
  have htrace : WordTrace (prefixWord ++ tailWord_6090799) baseStart_6090799 baseEnd_6090799 := by
    simpa [prefixWord, tailWord_6090799, baseEnd_6090799] using wordTrace_append hprefix tailTrace_6090799
  have hstable : (prefixWord ++ tailWord_6090799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090799).length < 2 ^ (prefixWord ++ tailWord_6090799).sum := by decide
  have hdescent : baseEnd_6090799 < baseStart_6090799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090814 : List Nat := [4, 2, 1, 3, 2, 2, 1, 2, 2, 2, 2]
def baseStart_6090814 : Nat := 118140960795 + 6090814 * 2 ^ 59
def prefixEnd_6090814 : Nat := 4983230072969 + 3 ^ 40 * 6090814 * 2
def baseEnd_6090814 : Nat := 3127515159134037895913863

theorem tailTrace_6090814 : CollatzResearch.WordTrace tailWord_6090814 prefixEnd_6090814 3127515159134037895913863 := by
  unfold tailWord_6090814
  simp only [CollatzResearch.WordTrace]
  refine ⟨27768779619503572632438937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148100157970685720706340997 27768779619503572632438937)
  ·
    refine ⟨20826584714627679474329203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27768779619503572632438937 20826584714627679474329203)
    ·
      refine ⟨31239877071941519211493805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20826584714627679474329203 31239877071941519211493805)
      ·
        refine ⟨11714953901978069704310177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31239877071941519211493805 11714953901978069704310177)
        ·
          refine ⟨8786215426483552278232633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11714953901978069704310177 8786215426483552278232633)
          ·
            refine ⟨6589661569862664208674475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8786215426483552278232633 6589661569862664208674475)
            ·
              refine ⟨9884492354793996313011713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6589661569862664208674475 9884492354793996313011713)
              ·
                refine ⟨7413369266095497234758785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9884492354793996313011713 7413369266095497234758785)
                ·
                  refine ⟨5560026949571622926069089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7413369266095497234758785 5560026949571622926069089)
                  ·
                    refine ⟨4170020212178717194551817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5560026949571622926069089 4170020212178717194551817)
                    ·
                      refine ⟨3127515159134037895913863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4170020212178717194551817 3127515159134037895913863)
                      ·
                        rfl

theorem cell23_6090814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_6090814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090814 prefixEnd_6090814 := by exact prefixLift 6090814
  have htrace : WordTrace (prefixWord ++ tailWord_6090814) baseStart_6090814 baseEnd_6090814 := by
    simpa [prefixWord, tailWord_6090814, baseEnd_6090814] using wordTrace_append hprefix tailTrace_6090814
  have hstable : (prefixWord ++ tailWord_6090814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090814).length < 2 ^ (prefixWord ++ tailWord_6090814).sum := by decide
  have hdescent : baseEnd_6090814 < baseStart_6090814 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090849 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 1, 6, 4]
def baseStart_6090849 : Nat := 118140960795 + 6090849 * 2 ^ 59
def prefixEnd_6090849 : Nat := 4983230072969 + 3 ^ 40 * 6090849 * 2
def baseEnd_6090849 : Nat := 3127533130956945258976201

theorem tailTrace_6090849 : CollatzResearch.WordTrace tailWord_6090849 prefixEnd_6090849 3127533130956945258976201 := by
  unfold tailWord_6090849
  simp only [CollatzResearch.WordTrace]
  refine ⟨222151513510901782037035601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148101009007267854691357067 222151513510901782037035601)
  ·
    refine ⟨166613635133176336527776701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222151513510901782037035601 166613635133176336527776701)
    ·
      refine ⟨62480113174941126197916263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166613635133176336527776701 62480113174941126197916263)
      ·
        refine ⟨93720169762411689296874395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62480113174941126197916263 93720169762411689296874395)
        ·
          refine ⟨140580254643617533945311593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93720169762411689296874395 140580254643617533945311593)
          ·
            refine ⟨105435190982713150458983695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140580254643617533945311593 105435190982713150458983695)
            ·
              refine ⟨158152786474069725688475543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105435190982713150458983695 158152786474069725688475543)
              ·
                refine ⟨237229179711104588532713315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158152786474069725688475543 237229179711104588532713315)
                ·
                  refine ⟨355843769566656882799069973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 237229179711104588532713315 355843769566656882799069973)
                  ·
                    refine ⟨16680176698437041381206405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 355843769566656882799069973 16680176698437041381206405)
                    ·
                      refine ⟨3127533130956945258976201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16680176698437041381206405 3127533130956945258976201)
                      ·
                        rfl

theorem cell23_6090849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_6090849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090849 prefixEnd_6090849 := by exact prefixLift 6090849
  have htrace : WordTrace (prefixWord ++ tailWord_6090849) baseStart_6090849 baseEnd_6090849 := by
    simpa [prefixWord, tailWord_6090849, baseEnd_6090849] using wordTrace_append hprefix tailTrace_6090849
  have hstable : (prefixWord ++ tailWord_6090849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090849).length < 2 ^ (prefixWord ++ tailWord_6090849).sum := by decide
  have hdescent : baseEnd_6090849 < baseStart_6090849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090873 : List Nat := [1, 2, 1, 3, 4, 2, 1, 2, 2, 2, 3]
def baseStart_6090873 : Nat := 118140960795 + 6090873 * 2 ^ 59
def prefixEnd_6090873 : Nat := 4983230072969 + 3 ^ 40 * 6090873 * 2
def baseEnd_6090873 : Nat := 3127545454492653165076091

theorem tailTrace_6090873 : CollatzResearch.WordTrace tailWord_6090873 prefixEnd_6090873 3127545454492653165076091 := by
  unfold tailWord_6090873
  simp only [CollatzResearch.WordTrace]
  refine ⟨222152388862814834135909273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148101592575209889423939515 222152388862814834135909273)
  ·
    refine ⟨166614291647111125601931955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222152388862814834135909273 166614291647111125601931955)
    ·
      refine ⟨249921437470666688402897933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166614291647111125601931955 249921437470666688402897933)
      ·
        refine ⟨93720539051500008151086725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249921437470666688402897933 93720539051500008151086725)
        ·
          refine ⟨17572601072156251528328761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93720539051500008151086725 17572601072156251528328761)
          ·
            refine ⟨13179450804117188646246571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17572601072156251528328761 13179450804117188646246571)
            ·
              refine ⟨19769176206175782969369857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13179450804117188646246571 19769176206175782969369857)
              ·
                refine ⟨14826882154631837227027393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19769176206175782969369857 14826882154631837227027393)
                ·
                  refine ⟨11120161615973877920270545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14826882154631837227027393 11120161615973877920270545)
                  ·
                    refine ⟨8340121211980408440202909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11120161615973877920270545 8340121211980408440202909)
                    ·
                      refine ⟨3127545454492653165076091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8340121211980408440202909 3127545454492653165076091)
                      ·
                        rfl

theorem cell23_6090873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 2, 3].length) (baseStart_6090873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090873 prefixEnd_6090873 := by exact prefixLift 6090873
  have htrace : WordTrace (prefixWord ++ tailWord_6090873) baseStart_6090873 baseEnd_6090873 := by
    simpa [prefixWord, tailWord_6090873, baseEnd_6090873] using wordTrace_append hprefix tailTrace_6090873
  have hstable : (prefixWord ++ tailWord_6090873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090873).length < 2 ^ (prefixWord ++ tailWord_6090873).sum := by decide
  have hdescent : baseEnd_6090873 < baseStart_6090873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6090994 : List Nat := [3, 2, 1, 3, 2, 1, 2, 4, 1, 2, 2]
def baseStart_6090994 : Nat := 118140960795 + 6090994 * 2 ^ 59
def prefixEnd_6090994 : Nat := 4983230072969 + 3 ^ 40 * 6090994 * 2
def baseEnd_6090994 : Nat := 3127607585651847191663035

theorem tailTrace_6090994 : CollatzResearch.WordTrace tailWord_6090994 prefixEnd_6090994 3127607585651847191663035 := by
  unfold tailWord_6090994
  simp only [CollatzResearch.WordTrace]
  refine ⟨55539200523844117950266009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148104534730250981200709357 55539200523844117950266009)
  ·
    refine ⟨41654400392883088462699507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55539200523844117950266009 41654400392883088462699507)
    ·
      refine ⟨62481600589324632694049261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41654400392883088462699507 62481600589324632694049261)
      ·
        refine ⟨23430600220996737260268473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62481600589324632694049261 23430600220996737260268473)
        ·
          refine ⟨17572950165747552945201355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23430600220996737260268473 17572950165747552945201355)
          ·
            refine ⟨26359425248621329417802033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17572950165747552945201355 26359425248621329417802033)
            ·
              refine ⟨19769568936465997063351525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26359425248621329417802033 19769568936465997063351525)
              ·
                refine ⟨3706794175587374449378411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19769568936465997063351525 3706794175587374449378411)
                ·
                  refine ⟨5560191263381061674067617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3706794175587374449378411 5560191263381061674067617)
                  ·
                    refine ⟨4170143447535796255550713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5560191263381061674067617 4170143447535796255550713)
                    ·
                      refine ⟨3127607585651847191663035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4170143447535796255550713 3127607585651847191663035)
                      ·
                        rfl

theorem cell23_6090994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_6090994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6090994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6090994 prefixEnd_6090994 := by exact prefixLift 6090994
  have htrace : WordTrace (prefixWord ++ tailWord_6090994) baseStart_6090994 baseEnd_6090994 := by
    simpa [prefixWord, tailWord_6090994, baseEnd_6090994] using wordTrace_append hprefix tailTrace_6090994
  have hstable : (prefixWord ++ tailWord_6090994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6090994).length < 2 ^ (prefixWord ++ tailWord_6090994).sum := by decide
  have hdescent : baseEnd_6090994 < baseStart_6090994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6090994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091056 : List Nat := [2, 1, 1, 1, 2, 2, 2, 5, 7]
def baseStart_6091056 : Nat := 118140960795 + 6091056 * 2 ^ 59
def prefixEnd_6091056 : Nat := 4983230072969 + 3 ^ 40 * 6091056 * 2
def baseEnd_6091056 : Nat := 347515491272491772120861

theorem tailTrace_6091056 : CollatzResearch.WordTrace tailWord_6091056 prefixEnd_6091056 347515491272491772120861 := by
  unfold tailWord_6091056
  simp only [CollatzResearch.WordTrace]
  refine ⟨111079531710575928194910511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148106042280767904259880681 111079531710575928194910511)
  ·
    refine ⟨166619297565863892292365767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111079531710575928194910511 166619297565863892292365767)
    ·
      refine ⟨249928946348795838438548651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166619297565863892292365767 249928946348795838438548651)
      ·
        refine ⟨374893419523193757657822977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249928946348795838438548651 374893419523193757657822977)
        ·
          refine ⟨281170064642395318243367233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374893419523193757657822977 281170064642395318243367233)
          ·
            refine ⟨210877548481796488682525425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281170064642395318243367233 210877548481796488682525425)
            ·
              refine ⟨158158161361347366511894069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210877548481796488682525425 158158161361347366511894069)
              ·
                refine ⟨14827327627626315610490069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 158158161361347366511894069 14827327627626315610490069)
                ·
                  refine ⟨347515491272491772120861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14827327627626315610490069 347515491272491772120861)
                  ·
                    rfl

theorem cell23_6091056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 7].length) (baseStart_6091056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091056 prefixEnd_6091056 := by exact prefixLift 6091056
  have htrace : WordTrace (prefixWord ++ tailWord_6091056) baseStart_6091056 baseEnd_6091056 := by
    simpa [prefixWord, tailWord_6091056, baseEnd_6091056] using wordTrace_append hprefix tailTrace_6091056
  have hstable : (prefixWord ++ tailWord_6091056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091056).length < 2 ^ (prefixWord ++ tailWord_6091056).sum := by decide
  have hdescent : baseEnd_6091056 < baseStart_6091056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091103 : List Nat := [1, 1, 2, 3, 1, 2, 4, 2, 2, 5]
def baseStart_6091103 : Nat := 118140960795 + 6091103 * 2 ^ 59
def prefixEnd_6091103 : Nat := 4983230072969 + 3 ^ 40 * 6091103 * 2
def baseEnd_6091103 : Nat := 1042554518347729088400011

theorem tailTrace_6091103 : CollatzResearch.WordTrace tailWord_6091103 prefixEnd_6091103 1042554518347729088400011 := by
  unfold tailWord_6091103
  simp only [CollatzResearch.WordTrace]
  refine ⟨222160777651981583416781963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148107185101321055611187975 222160777651981583416781963)
  ·
    refine ⟨333241166477972375125172945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222160777651981583416781963 333241166477972375125172945)
    ·
      refine ⟨249930874858479281343879709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333241166477972375125172945 249930874858479281343879709)
      ·
        refine ⟨93724078071929730503954891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249930874858479281343879709 93724078071929730503954891)
        ·
          refine ⟨140586117107894595755932337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93724078071929730503954891 140586117107894595755932337)
          ·
            refine ⟨105439587830920946816949253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140586117107894595755932337 105439587830920946816949253)
            ·
              refine ⟨19769922718297677528177985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105439587830920946816949253 19769922718297677528177985)
              ·
                refine ⟨14827442038723258146133489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19769922718297677528177985 14827442038723258146133489)
                ·
                  refine ⟨11120581529042443609600117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14827442038723258146133489 11120581529042443609600117)
                  ·
                    refine ⟨1042554518347729088400011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11120581529042443609600117 1042554518347729088400011)
                    ·
                      rfl

theorem cell23_6091103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 5].length) (baseStart_6091103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091103 prefixEnd_6091103 := by exact prefixLift 6091103
  have htrace : WordTrace (prefixWord ++ tailWord_6091103) baseStart_6091103 baseEnd_6091103 := by
    simpa [prefixWord, tailWord_6091103, baseEnd_6091103] using wordTrace_append hprefix tailTrace_6091103
  have hstable : (prefixWord ++ tailWord_6091103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091103).length < 2 ^ (prefixWord ++ tailWord_6091103).sum := by decide
  have hdescent : baseEnd_6091103 < baseStart_6091103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091137 : List Nat := [1, 2, 4, 3, 1, 3, 1, 1, 2, 5]
def baseStart_6091137 : Nat := 118140960795 + 6091137 * 2 ^ 59
def prefixEnd_6091137 : Nat := 4983230072969 + 3 ^ 40 * 6091137 * 2
def baseEnd_6091137 : Nat := 1042560337795146710724959

theorem tailTrace_6091137 : CollatzResearch.WordTrace tailWord_6091137 prefixEnd_6091137 1042560337795146710724959 := by
  unfold tailWord_6091137
  simp only [CollatzResearch.WordTrace]
  refine ⟨222162017733858407223519665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148108011822572271482346443 222162017733858407223519665)
  ·
    refine ⟨166621513300393805417639749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222162017733858407223519665 166621513300393805417639749)
    ·
      refine ⟨31241533743823838515807453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166621513300393805417639749 31241533743823838515807453)
      ·
        refine ⟨11715575153933939443427795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31241533743823838515807453 11715575153933939443427795)
        ·
          refine ⟨17573362730900909165141693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11715575153933939443427795 17573362730900909165141693)
          ·
            refine ⟨6590011024087840936928135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17573362730900909165141693 6590011024087840936928135)
            ·
              refine ⟨9885016536131761405392203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6590011024087840936928135 9885016536131761405392203)
              ·
                refine ⟨14827524804197642108088305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9885016536131761405392203 14827524804197642108088305)
                ·
                  refine ⟨11120643603148231581066229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14827524804197642108088305 11120643603148231581066229)
                  ·
                    refine ⟨1042560337795146710724959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11120643603148231581066229 1042560337795146710724959)
                    ·
                      rfl

theorem cell23_6091137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_6091137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091137 prefixEnd_6091137 := by exact prefixLift 6091137
  have htrace : WordTrace (prefixWord ++ tailWord_6091137) baseStart_6091137 baseEnd_6091137 := by
    simpa [prefixWord, tailWord_6091137, baseEnd_6091137] using wordTrace_append hprefix tailTrace_6091137
  have hstable : (prefixWord ++ tailWord_6091137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091137).length < 2 ^ (prefixWord ++ tailWord_6091137).sum := by decide
  have hdescent : baseEnd_6091137 < baseStart_6091137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091140 : List Nat := [2, 3, 2, 1, 1, 2, 1, 2, 1, 6, 2]
def baseStart_6091140 : Nat := 118140960795 + 6091140 * 2 ^ 59
def prefixEnd_6091140 : Nat := 4983230072969 + 3 ^ 40 * 6091140 * 2
def baseEnd_6091140 : Nat := 3127682553827403620437363

theorem tailTrace_6091140 : CollatzResearch.WordTrace tailWord_6091140 prefixEnd_6091140 3127682553827403620437363 := by
  unfold tailWord_6091140
  simp only [CollatzResearch.WordTrace]
  refine ⟨111081063576423769367939437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148108084768565025823919249 111081063576423769367939437)
  ·
    refine ⟨41655398841158913512977289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111081063576423769367939437 41655398841158913512977289)
    ·
      refine ⟨31241549130869185134732967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41655398841158913512977289 31241549130869185134732967)
      ·
        refine ⟨46862323696303777702099451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31241549130869185134732967 46862323696303777702099451)
        ·
          refine ⟨70293485544455666553149177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46862323696303777702099451 70293485544455666553149177)
          ·
            refine ⟨52720114158341749914861883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70293485544455666553149177 52720114158341749914861883)
            ·
              refine ⟨79080171237512624872292825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52720114158341749914861883 79080171237512624872292825)
              ·
                refine ⟨59310128428134468654219619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79080171237512624872292825 59310128428134468654219619)
                ·
                  refine ⟨88965192642201702981329429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59310128428134468654219619 88965192642201702981329429)
                  ·
                    refine ⟨4170243405103204827249817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 88965192642201702981329429 4170243405103204827249817)
                    ·
                      refine ⟨3127682553827403620437363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4170243405103204827249817 3127682553827403620437363)
                      ·
                        rfl

theorem cell23_6091140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_6091140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091140 prefixEnd_6091140 := by exact prefixLift 6091140
  have htrace : WordTrace (prefixWord ++ tailWord_6091140) baseStart_6091140 baseEnd_6091140 := by
    simpa [prefixWord, tailWord_6091140, baseEnd_6091140] using wordTrace_append hprefix tailTrace_6091140
  have hstable : (prefixWord ++ tailWord_6091140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091140).length < 2 ^ (prefixWord ++ tailWord_6091140).sum := by decide
  have hdescent : baseEnd_6091140 < baseStart_6091140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091167 : List Nat := [1, 1, 2, 5, 1, 1, 1, 6, 1, 4]
def baseStart_6091167 : Nat := 118140960795 + 6091167 * 2 ^ 59
def prefixEnd_6091167 : Nat := 4983230072969 + 3 ^ 40 * 6091167 * 2
def baseEnd_6091167 : Nat := 1042565472601691671599913

theorem tailTrace_6091167 : CollatzResearch.WordTrace tailWord_6091167 prefixEnd_6091167 1042565472601691671599913 := by
  unfold tailWord_6091167
  simp only [CollatzResearch.WordTrace]
  refine ⟨222163111923749722347111755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148108741282499814898074503 222163111923749722347111755)
  ·
    refine ⟨333244667885624583520667633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222163111923749722347111755 333244667885624583520667633)
    ·
      refine ⟨249933500914218437640500725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333244667885624583520667633 249933500914218437640500725)
      ·
        refine ⟨23431265710707978528796943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 249933500914218437640500725 23431265710707978528796943)
        ·
          refine ⟨35146898566061967793195415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23431265710707978528796943 35146898566061967793195415)
          ·
            refine ⟨52720347849092951689793123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35146898566061967793195415 52720347849092951689793123)
            ·
              refine ⟨79080521773639427534689685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52720347849092951689793123 79080521773639427534689685)
              ·
                refine ⟨3706899458139348165688579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 79080521773639427534689685 3706899458139348165688579)
                ·
                  refine ⟨5560349187209022248532869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3706899458139348165688579 5560349187209022248532869)
                  ·
                    refine ⟨1042565472601691671599913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5560349187209022248532869 1042565472601691671599913)
                    ·
                      rfl

theorem cell23_6091167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 6, 1, 4].length) (baseStart_6091167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091167 prefixEnd_6091167 := by exact prefixLift 6091167
  have htrace : WordTrace (prefixWord ++ tailWord_6091167) baseStart_6091167 baseEnd_6091167 := by
    simpa [prefixWord, tailWord_6091167, baseEnd_6091167] using wordTrace_append hprefix tailTrace_6091167
  have hstable : (prefixWord ++ tailWord_6091167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091167).length < 2 ^ (prefixWord ++ tailWord_6091167).sum := by decide
  have hdescent : baseEnd_6091167 < baseStart_6091167 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091210 : List Nat := [3, 1, 2, 1, 2, 2, 1, 5, 1, 5]
def baseStart_6091210 : Nat := 118140960795 + 6091210 * 2 ^ 59
def prefixEnd_6091210 : Nat := 4983230072969 + 3 ^ 40 * 6091210 * 2
def baseEnd_6091210 : Nat := 1042572832491072782187347

theorem tailTrace_6091210 : CollatzResearch.WordTrace tailWord_6091210 prefixEnd_6091210 1042572832491072782187347 := by
  unfold tailWord_6091210
  simp only [CollatzResearch.WordTrace]
  refine ⟨55541170065648485172731771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148109786841729293793951389 55541170065648485172731771)
  ·
    refine ⟨83311755098472727759097657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55541170065648485172731771 83311755098472727759097657)
    ·
      refine ⟨62483816323854545819323243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83311755098472727759097657 62483816323854545819323243)
      ·
        refine ⟨93725724485781818728984865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62483816323854545819323243 93725724485781818728984865)
        ·
          refine ⟨70294293364336364046738649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93725724485781818728984865 70294293364336364046738649)
          ·
            refine ⟨52720720023252273035053987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70294293364336364046738649 52720720023252273035053987)
            ·
              refine ⟨79081080034878409552580981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52720720023252273035053987 79081080034878409552580981)
              ·
                refine ⟨7413851253269850895554467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79081080034878409552580981 7413851253269850895554467)
                ·
                  refine ⟨11120776879904776343331701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7413851253269850895554467 11120776879904776343331701)
                  ·
                    refine ⟨1042572832491072782187347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11120776879904776343331701 1042572832491072782187347)
                    ·
                      rfl

theorem cell23_6091210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 5, 1, 5].length) (baseStart_6091210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091210 prefixEnd_6091210 := by exact prefixLift 6091210
  have htrace : WordTrace (prefixWord ++ tailWord_6091210) baseStart_6091210 baseEnd_6091210 := by
    simpa [prefixWord, tailWord_6091210, baseEnd_6091210] using wordTrace_append hprefix tailTrace_6091210
  have hstable : (prefixWord ++ tailWord_6091210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091210).length < 2 ^ (prefixWord ++ tailWord_6091210).sum := by decide
  have hdescent : baseEnd_6091210 < baseStart_6091210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091218 : List Nat := [3, 2, 2, 4, 1, 1, 3, 2, 1, 4]
def baseStart_6091218 : Nat := 118140960795 + 6091218 * 2 ^ 59
def prefixEnd_6091218 : Nat := 4983230072969 + 3 ^ 40 * 6091218 * 2
def baseEnd_6091218 : Nat := 1042574201772818105087335

theorem tailTrace_6091218 : CollatzResearch.WordTrace tailWord_6091218 prefixEnd_6091218 1042574201772818105087335 := by
  unfold tailWord_6091218
  simp only [CollatzResearch.WordTrace]
  refine ⟨55541243011641239514304577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148109981364376638704812205 55541243011641239514304577)
  ·
    refine ⟨41655932258730929635728433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55541243011641239514304577 41655932258730929635728433)
    ·
      refine ⟨31241949194048197226796325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41655932258730929635728433 31241949194048197226796325)
      ·
        refine ⟨5857865473884036980024311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31241949194048197226796325 5857865473884036980024311)
        ·
          refine ⟨8786798210826055470036467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5857865473884036980024311 8786798210826055470036467)
          ·
            refine ⟨13180197316239083205054701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8786798210826055470036467 13180197316239083205054701)
            ·
              refine ⟨4942573993589656201895513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13180197316239083205054701 4942573993589656201895513)
              ·
                refine ⟨3706930495192242151421635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4942573993589656201895513 3706930495192242151421635)
                ·
                  refine ⟨5560395742788363227132453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3706930495192242151421635 5560395742788363227132453)
                  ·
                    refine ⟨1042574201772818105087335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5560395742788363227132453 1042574201772818105087335)
                    ·
                      rfl

theorem cell23_6091218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_6091218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091218 prefixEnd_6091218 := by exact prefixLift 6091218
  have htrace : WordTrace (prefixWord ++ tailWord_6091218) baseStart_6091218 baseEnd_6091218 := by
    simpa [prefixWord, tailWord_6091218, baseEnd_6091218] using wordTrace_append hprefix tailTrace_6091218
  have hstable : (prefixWord ++ tailWord_6091218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091218).length < 2 ^ (prefixWord ++ tailWord_6091218).sum := by decide
  have hdescent : baseEnd_6091218 < baseStart_6091218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091243 : List Nat := [1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 6]
def baseStart_6091243 : Nat := 118140960795 + 6091243 * 2 ^ 59
def prefixEnd_6091243 : Nat := 4983230072969 + 3 ^ 40 * 6091243 * 2
def baseEnd_6091243 : Nat := 3127735442334816717449389

theorem tailTrace_6091243 : CollatzResearch.WordTrace tailWord_6091243 prefixEnd_6091243 3127735442334816717449389 := by
  unfold tailWord_6091243
  simp only [CollatzResearch.WordTrace]
  refine ⟨222165883871474387326878383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148110589247649591551252255 222165883871474387326878383)
  ·
    refine ⟨333248825807211580990317575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222165883871474387326878383 333248825807211580990317575)
    ·
      refine ⟨499873238710817371485476363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333248825807211580990317575 499873238710817371485476363)
      ·
        refine ⟨749809858066226057228214545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 499873238710817371485476363 749809858066226057228214545)
        ·
          refine ⟨562357393549669542921160909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 749809858066226057228214545 562357393549669542921160909)
          ·
            refine ⟨210884022581126078595435341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 562357393549669542921160909 210884022581126078595435341)
            ·
              refine ⟨79081508467922279473288253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 210884022581126078595435341 79081508467922279473288253)
              ·
                refine ⟨29655565675470854802483095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79081508467922279473288253 29655565675470854802483095)
                ·
                  refine ⟨44483348513206282203724643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29655565675470854802483095 44483348513206282203724643)
                  ·
                    refine ⟨66725022769809423305586965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44483348513206282203724643 66725022769809423305586965)
                    ·
                      refine ⟨3127735442334816717449389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66725022769809423305586965 3127735442334816717449389)
                      ·
                        rfl

theorem cell23_6091243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 1, 6].length) (baseStart_6091243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091243 prefixEnd_6091243 := by exact prefixLift 6091243
  have htrace : WordTrace (prefixWord ++ tailWord_6091243) baseStart_6091243 baseEnd_6091243 := by
    simpa [prefixWord, tailWord_6091243, baseEnd_6091243] using wordTrace_append hprefix tailTrace_6091243
  have hstable : (prefixWord ++ tailWord_6091243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091243).length < 2 ^ (prefixWord ++ tailWord_6091243).sum := by decide
  have hdescent : baseEnd_6091243 < baseStart_6091243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091247 : List Nat := [1, 1, 2, 1, 4, 1, 1, 3, 5, 2, 2]
def baseStart_6091247 : Nat := 118140960795 + 6091247 * 2 ^ 59
def prefixEnd_6091247 : Nat := 4983230072969 + 3 ^ 40 * 6091247 * 2
def baseEnd_6091247 : Nat := 3127737496257434701799371

theorem tailTrace_6091247 : CollatzResearch.WordTrace tailWord_6091247 prefixEnd_6091247 3127737496257434701799371 := by
  unfold tailWord_6091247
  simp only [CollatzResearch.WordTrace]
  refine ⟨222166029763459896010023995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148110686508973264006682663 222166029763459896010023995)
  ·
    refine ⟨333249044645189844015035993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222166029763459896010023995 333249044645189844015035993)
    ·
      refine ⟨249936783483892383011276995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333249044645189844015035993 249936783483892383011276995)
      ·
        refine ⟨374905175225838574516915493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249936783483892383011276995 374905175225838574516915493)
        ·
          refine ⟨70294720354844732721921655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 374905175225838574516915493 70294720354844732721921655)
          ·
            refine ⟨105442080532267099082882483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70294720354844732721921655 105442080532267099082882483)
            ·
              refine ⟨158163120798400648624323725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105442080532267099082882483 158163120798400648624323725)
              ·
                refine ⟨59311170299400243234121397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158163120798400648624323725 59311170299400243234121397)
                ·
                  refine ⟨5560422215568772803198881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59311170299400243234121397 5560422215568772803198881)
                  ·
                    refine ⟨4170316661676579602399161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5560422215568772803198881 4170316661676579602399161)
                    ·
                      refine ⟨3127737496257434701799371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4170316661676579602399161 3127737496257434701799371)
                      ·
                        rfl

theorem cell23_6091247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 3, 5, 2, 2].length) (baseStart_6091247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091247 prefixEnd_6091247 := by exact prefixLift 6091247
  have htrace : WordTrace (prefixWord ++ tailWord_6091247) baseStart_6091247 baseEnd_6091247 := by
    simpa [prefixWord, tailWord_6091247, baseEnd_6091247] using wordTrace_append hprefix tailTrace_6091247
  have hstable : (prefixWord ++ tailWord_6091247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091247).length < 2 ^ (prefixWord ++ tailWord_6091247).sum := by decide
  have hdescent : baseEnd_6091247 < baseStart_6091247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091273 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 2, 2, 6]
def baseStart_6091273 : Nat := 118140960795 + 6091273 * 2 ^ 59
def prefixEnd_6091273 : Nat := 4983230072969 + 3 ^ 40 * 6091273 * 2
def baseEnd_6091273 : Nat := 3127750846754451600074251

theorem tailTrace_6091273 : CollatzResearch.WordTrace tailWord_6091273 prefixEnd_6091273 3127750846754451600074251 := by
  unfold tailWord_6091273
  simp only [CollatzResearch.WordTrace]
  refine ⟨222166978061365702450470473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148111318707577134966980315 222166978061365702450470473)
  ·
    refine ⟨166625233546024276837852855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222166978061365702450470473 166625233546024276837852855)
    ·
      refine ⟨249937850319036415256779283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166625233546024276837852855 249937850319036415256779283)
      ·
        refine ⟨374906775478554622885168925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249937850319036415256779283 374906775478554622885168925)
        ·
          refine ⟨140590040804457983581938347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 374906775478554622885168925 140590040804457983581938347)
          ·
            refine ⟨210885061206686975372907521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140590040804457983581938347 210885061206686975372907521)
            ·
              refine ⟨158163795905015231529680641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210885061206686975372907521 158163795905015231529680641)
              ·
                refine ⟨118622846928761423647260481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158163795905015231529680641 118622846928761423647260481)
                ·
                  refine ⟨88967135196571067735445361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118622846928761423647260481 88967135196571067735445361)
                  ·
                    refine ⟨66725351397428300801584021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88967135196571067735445361 66725351397428300801584021)
                    ·
                      refine ⟨3127750846754451600074251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66725351397428300801584021 3127750846754451600074251)
                      ·
                        rfl

theorem cell23_6091273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 2, 6].length) (baseStart_6091273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091273 prefixEnd_6091273 := by exact prefixLift 6091273
  have htrace : WordTrace (prefixWord ++ tailWord_6091273) baseStart_6091273 baseEnd_6091273 := by
    simpa [prefixWord, tailWord_6091273, baseEnd_6091273] using wordTrace_append hprefix tailTrace_6091273
  have hstable : (prefixWord ++ tailWord_6091273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091273).length < 2 ^ (prefixWord ++ tailWord_6091273).sum := by decide
  have hdescent : baseEnd_6091273 < baseStart_6091273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091283 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 1, 9]
def baseStart_6091283 : Nat := 118140960795 + 6091283 * 2 ^ 59
def prefixEnd_6091283 : Nat := 4983230072969 + 3 ^ 40 * 6091283 * 2
def baseEnd_6091283 : Nat := 1042585327186998853649735

theorem tailTrace_6091283 : CollatzResearch.WordTrace tailWord_6091283 prefixEnd_6091283 1042585327186998853649735 := by
  unfold tailWord_6091283
  simp only [CollatzResearch.WordTrace]
  refine ⟨222167342791329474158334503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148111561860886316105556335 222167342791329474158334503)
  ·
    refine ⟨333251014186994211237501755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222167342791329474158334503 333251014186994211237501755)
    ·
      refine ⟨499876521280491316856252633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333251014186994211237501755 499876521280491316856252633)
      ·
        refine ⟨374907390960368487642189475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 499876521280491316856252633 374907390960368487642189475)
        ·
          refine ⟨562361086440552731463284213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374907390960368487642189475 562361086440552731463284213)
          ·
            refine ⟨52721351853801818574682895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 562361086440552731463284213 52721351853801818574682895)
            ·
              refine ⟨79082027780702727862024343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52721351853801818574682895 79082027780702727862024343)
              ·
                refine ⟨118623041671054091793036515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79082027780702727862024343 118623041671054091793036515)
                ·
                  refine ⟨177934562506581137689554773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118623041671054091793036515 177934562506581137689554773)
                  ·
                    refine ⟨1042585327186998853649735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 177934562506581137689554773 1042585327186998853649735)
                    ·
                      rfl

theorem cell23_6091283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 9].length) (baseStart_6091283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091283 prefixEnd_6091283 := by exact prefixLift 6091283
  have htrace : WordTrace (prefixWord ++ tailWord_6091283) baseStart_6091283 baseEnd_6091283 := by
    simpa [prefixWord, tailWord_6091283, baseEnd_6091283] using wordTrace_append hprefix tailTrace_6091283
  have hstable : (prefixWord ++ tailWord_6091283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091283).length < 2 ^ (prefixWord ++ tailWord_6091283).sum := by decide
  have hdescent : baseEnd_6091283 < baseStart_6091283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091284 : List Nat := [2, 4, 3, 1, 1, 1, 1, 2, 3, 2, 3]
def baseStart_6091284 : Nat := 118140960795 + 6091284 * 2 ^ 59
def prefixEnd_6091284 : Nat := 4983230072969 + 3 ^ 40 * 6091284 * 2
def baseEnd_6091284 : Nat := 3127756495041651057036701

theorem tailTrace_6091284 : CollatzResearch.WordTrace tailWord_6091284 prefixEnd_6091284 3127756495041651057036701 := by
  unfold tailWord_6091284
  simp only [CollatzResearch.WordTrace]
  refine ⟨111083689632162925664560453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148111586176217234219413937 111083689632162925664560453)
  ·
    refine ⟨20828191806030548562105085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111083689632162925664560453 20828191806030548562105085)
    ·
      refine ⟨7810571927261455710789407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20828191806030548562105085 7810571927261455710789407)
      ·
        refine ⟨11715857890892183566184111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7810571927261455710789407 11715857890892183566184111)
        ·
          refine ⟨17573786836338275349276167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11715857890892183566184111 17573786836338275349276167)
          ·
            refine ⟨26360680254507413023914251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17573786836338275349276167 26360680254507413023914251)
            ·
              refine ⟨39541020381761119535871377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26360680254507413023914251 39541020381761119535871377)
              ·
                refine ⟨29655765286320839651903533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39541020381761119535871377 29655765286320839651903533)
                ·
                  refine ⟨11120911982370314869463825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29655765286320839651903533 11120911982370314869463825)
                  ·
                    refine ⟨8340683986777736152097869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11120911982370314869463825 8340683986777736152097869)
                    ·
                      refine ⟨3127756495041651057036701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8340683986777736152097869 3127756495041651057036701)
                      ·
                        rfl

theorem cell23_6091284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_6091284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091284 prefixEnd_6091284 := by exact prefixLift 6091284
  have htrace : WordTrace (prefixWord ++ tailWord_6091284) baseStart_6091284 baseEnd_6091284 := by
    simpa [prefixWord, tailWord_6091284, baseEnd_6091284] using wordTrace_append hprefix tailTrace_6091284
  have hstable : (prefixWord ++ tailWord_6091284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091284).length < 2 ^ (prefixWord ++ tailWord_6091284).sum := by decide
  have hdescent : baseEnd_6091284 < baseStart_6091284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091297 : List Nat := [1, 2, 3, 2, 2, 1, 4, 1, 1, 3, 3]
def baseStart_6091297 : Nat := 118140960795 + 6091297 * 2 ^ 59
def prefixEnd_6091297 : Nat := 4983230072969 + 3 ^ 40 * 6091297 * 2
def baseEnd_6091297 : Nat := 3127763170290159506174141

theorem tailTrace_6091297 : CollatzResearch.WordTrace tailWord_6091297 prefixEnd_6091297 3127763170290159506174141 := by
  unfold tailWord_6091297
  simp only [CollatzResearch.WordTrace]
  refine ⟨222167853413278754549344145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148111902275519169699562763 222167853413278754549344145)
  ·
    refine ⟨166625890059959065912008109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222167853413278754549344145 166625890059959065912008109)
    ·
      refine ⟨62484708772484649717003041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 166625890059959065912008109 62484708772484649717003041)
      ·
        refine ⟨46863531579363487287752281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62484708772484649717003041 46863531579363487287752281)
        ·
          refine ⟨35147648684522615465814211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46863531579363487287752281 35147648684522615465814211)
          ·
            refine ⟨52721473026783923198721317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35147648684522615465814211 52721473026783923198721317)
            ·
              refine ⟨9885276192521985599760247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52721473026783923198721317 9885276192521985599760247)
              ·
                refine ⟨14827914288782978399640371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9885276192521985599760247 14827914288782978399640371)
                ·
                  refine ⟨22241871433174467599460557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14827914288782978399640371 22241871433174467599460557)
                  ·
                    refine ⟨8340701787440425349797709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22241871433174467599460557 8340701787440425349797709)
                    ·
                      refine ⟨3127763170290159506174141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8340701787440425349797709 3127763170290159506174141)
                      ·
                        rfl

theorem cell23_6091297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_6091297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091297 prefixEnd_6091297 := by exact prefixLift 6091297
  have htrace : WordTrace (prefixWord ++ tailWord_6091297) baseStart_6091297 baseEnd_6091297 := by
    simpa [prefixWord, tailWord_6091297, baseEnd_6091297] using wordTrace_append hprefix tailTrace_6091297
  have hstable : (prefixWord ++ tailWord_6091297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091297).length < 2 ^ (prefixWord ++ tailWord_6091297).sum := by decide
  have hdescent : baseEnd_6091297 < baseStart_6091297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091318 : List Nat := [5, 1, 2, 1, 2, 3, 2, 1, 1, 2, 3]
def baseStart_6091318 : Nat := 118140960795 + 6091318 * 2 ^ 59
def prefixEnd_6091318 : Nat := 4983230072969 + 3 ^ 40 * 6091318 * 2
def baseEnd_6091318 : Nat := 3127773953383903924011545

theorem tailTrace_6091318 : CollatzResearch.WordTrace tailWord_6091318 prefixEnd_6091318 3127773953383903924011545 := by
  unfold tailWord_6091318
  simp only [CollatzResearch.WordTrace]
  refine ⟨13885538709137667195991163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148112412897468450090572405 13885538709137667195991163)
  ·
    refine ⟨20828308063706500793986745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13885538709137667195991163 20828308063706500793986745)
    ·
      refine ⟨15621231047779875595490059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20828308063706500793986745 15621231047779875595490059)
      ·
        refine ⟨23431846571669813393235089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15621231047779875595490059 23431846571669813393235089)
        ·
          refine ⟨17573884928752360044926317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23431846571669813393235089 17573884928752360044926317)
          ·
            refine ⟨6590206848282135016847369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17573884928752360044926317 6590206848282135016847369)
            ·
              refine ⟨4942655136211601262635527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6590206848282135016847369 4942655136211601262635527)
              ·
                refine ⟨7413982704317401893953291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4942655136211601262635527 7413982704317401893953291)
                ·
                  refine ⟨11120974056476102840929937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7413982704317401893953291 11120974056476102840929937)
                  ·
                    refine ⟨8340730542357077130697453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11120974056476102840929937 8340730542357077130697453)
                    ·
                      refine ⟨3127773953383903924011545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8340730542357077130697453 3127773953383903924011545)
                      ·
                        rfl

theorem cell23_6091318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_6091318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091318 prefixEnd_6091318 := by exact prefixLift 6091318
  have htrace : WordTrace (prefixWord ++ tailWord_6091318) baseStart_6091318 baseEnd_6091318 := by
    simpa [prefixWord, tailWord_6091318, baseEnd_6091318] using wordTrace_append hprefix tailTrace_6091318
  have hstable : (prefixWord ++ tailWord_6091318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091318).length < 2 ^ (prefixWord ++ tailWord_6091318).sum := by decide
  have hdescent : baseEnd_6091318 < baseStart_6091318 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091323 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 9]
def baseStart_6091323 : Nat := 118140960795 + 6091323 * 2 ^ 59
def prefixEnd_6091323 : Nat := 4983230072969 + 3 ^ 40 * 6091323 * 2
def baseEnd_6091323 : Nat := 3127776520787176404449021

theorem tailTrace_6091323 : CollatzResearch.WordTrace tailWord_6091323 prefixEnd_6091323 3127776520787176404449021 := by
  unfold tailWord_6091323
  simp only [CollatzResearch.WordTrace]
  refine ⟨222168801711184560989790623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148112534474123040659860415 222168801711184560989790623)
  ·
    refine ⟨333253202566776841484685935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222168801711184560989790623 333253202566776841484685935)
    ·
      refine ⟨499879803850165262227028903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333253202566776841484685935 499879803850165262227028903)
      ·
        refine ⟨749819705775247893340543355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 499879803850165262227028903 749819705775247893340543355)
        ·
          refine ⟨1124729558662871840010815033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 749819705775247893340543355 1124729558662871840010815033)
          ·
            refine ⟨843547168997153880008111275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1124729558662871840010815033 843547168997153880008111275)
            ·
              refine ⟨1265320753495730820012166913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 843547168997153880008111275 1265320753495730820012166913)
              ·
                refine ⟨948990565121798115009125185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1265320753495730820012166913 948990565121798115009125185)
                ·
                  refine ⟨711742923841348586256843889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 948990565121798115009125185 711742923841348586256843889)
                  ·
                    refine ⟨533807192881011439692632917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 711742923841348586256843889 533807192881011439692632917)
                    ·
                      refine ⟨3127776520787176404449021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 533807192881011439692632917 3127776520787176404449021)
                      ·
                        rfl

theorem cell23_6091323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 9].length) (baseStart_6091323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091323 prefixEnd_6091323 := by exact prefixLift 6091323
  have htrace : WordTrace (prefixWord ++ tailWord_6091323) baseStart_6091323 baseEnd_6091323 := by
    simpa [prefixWord, tailWord_6091323, baseEnd_6091323] using wordTrace_append hprefix tailTrace_6091323
  have hstable : (prefixWord ++ tailWord_6091323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091323).length < 2 ^ (prefixWord ++ tailWord_6091323).sum := by decide
  have hdescent : baseEnd_6091323 < baseStart_6091323 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091360 : List Nat := [2, 1, 1, 3, 2, 1, 4, 2, 7]
def baseStart_6091360 : Nat := 118140960795 + 6091360 * 2 ^ 59
def prefixEnd_6091360 : Nat := 4983230072969 + 3 ^ 40 * 6091360 * 2
def baseEnd_6091360 : Nat := 347532835507932528854039

theorem tailTrace_6091360 : CollatzResearch.WordTrace tailWord_6091360 prefixEnd_6091360 347532835507932528854039 := by
  unfold tailWord_6091360
  simp only [CollatzResearch.WordTrace]
  refine ⟨111085075606025258154443767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148113434141367010872591689 111085075606025258154443767)
  ·
    refine ⟨166627613409037887231665651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111085075606025258154443767 166627613409037887231665651)
    ·
      refine ⟨249941420113556830847498477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166627613409037887231665651 249941420113556830847498477)
      ·
        refine ⟨93728032542583811567811929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 249941420113556830847498477 93728032542583811567811929)
        ·
          refine ⟨70296024406937858675858947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93728032542583811567811929 70296024406937858675858947)
          ·
            refine ⟨105444036610406788013788421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70296024406937858675858947 105444036610406788013788421)
            ·
              refine ⟨19770756864451272752585329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105444036610406788013788421 19770756864451272752585329)
              ·
                refine ⟨14828067648338454564438997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19770756864451272752585329 14828067648338454564438997)
                ·
                  refine ⟨347532835507932528854039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14828067648338454564438997 347532835507932528854039)
                  ·
                    rfl

theorem cell23_6091360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 7].length) (baseStart_6091360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091360 prefixEnd_6091360 := by exact prefixLift 6091360
  have htrace : WordTrace (prefixWord ++ tailWord_6091360) baseStart_6091360 baseEnd_6091360 := by
    simpa [prefixWord, tailWord_6091360, baseEnd_6091360] using wordTrace_append hprefix tailTrace_6091360
  have hstable : (prefixWord ++ tailWord_6091360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091360).length < 2 ^ (prefixWord ++ tailWord_6091360).sum := by decide
  have hdescent : baseEnd_6091360 < baseStart_6091360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091424 : List Nat := [2, 1, 1, 4, 4, 1, 2, 1, 2, 5]
def baseStart_6091424 : Nat := 118140960795 + 6091424 * 2 ^ 59
def prefixEnd_6091424 : Nat := 4983230072969 + 3 ^ 40 * 6091424 * 2
def baseEnd_6091424 : Nat := 1042609460777760169762019

theorem tailTrace_6091424 : CollatzResearch.WordTrace tailWord_6091424 prefixEnd_6091424 1042609460777760169762019 := by
  unfold tailWord_6091424
  simp only [CollatzResearch.WordTrace]
  refine ⟨111086242741909327619608663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148114990322545770159478217 111086242741909327619608663)
  ·
    refine ⟨166629364112863991429412995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111086242741909327619608663 166629364112863991429412995)
    ·
      refine ⟨249944046169295987144119493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166629364112863991429412995 249944046169295987144119493)
      ·
        refine ⟨46864508656742997589522405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 249944046169295987144119493 46864508656742997589522405)
        ·
          refine ⟨8787095373139312048035451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46864508656742997589522405 8787095373139312048035451)
          ·
            refine ⟨13180643059708968072053177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8787095373139312048035451 13180643059708968072053177)
            ·
              refine ⟨9885482294781726054039883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13180643059708968072053177 9885482294781726054039883)
              ·
                refine ⟨14828223442172589081059825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9885482294781726054039883 14828223442172589081059825)
                ·
                  refine ⟨11121167581629441810794869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14828223442172589081059825 11121167581629441810794869)
                  ·
                    refine ⟨1042609460777760169762019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11121167581629441810794869 1042609460777760169762019)
                    ·
                      rfl

theorem cell23_6091424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 2, 5].length) (baseStart_6091424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091424 prefixEnd_6091424 := by exact prefixLift 6091424
  have htrace : WordTrace (prefixWord ++ tailWord_6091424) baseStart_6091424 baseEnd_6091424 := by
    simpa [prefixWord, tailWord_6091424, baseEnd_6091424] using wordTrace_append hprefix tailTrace_6091424
  have hstable : (prefixWord ++ tailWord_6091424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091424).length < 2 ^ (prefixWord ++ tailWord_6091424).sum := by decide
  have hdescent : baseEnd_6091424 < baseStart_6091424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091427 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 3, 6, 2]
def baseStart_6091427 : Nat := 118140960795 + 6091427 * 2 ^ 59
def prefixEnd_6091427 : Nat := 4983230072969 + 3 ^ 40 * 6091427 * 2
def baseEnd_6091427 : Nat := 3127829922775243997548543

theorem tailTrace_6091427 : CollatzResearch.WordTrace tailWord_6091427 prefixEnd_6091427 3127829922775243997548543 := by
  unfold tailWord_6091427
  simp only [CollatzResearch.WordTrace]
  refine ⟨222172594902807786751576535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148115063268538524501051023 222172594902807786751576535)
  ·
    refine ⟨333258892354211680127364803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222172594902807786751576535 333258892354211680127364803)
    ·
      refine ⟨499888338531317520191047205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333258892354211680127364803 499888338531317520191047205)
      ·
        refine ⟨93729063474622035035821351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 499888338531317520191047205 93729063474622035035821351)
        ·
          refine ⟨140593595211933052553732027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93729063474622035035821351 140593595211933052553732027)
          ·
            refine ⟨210890392817899578830598041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140593595211933052553732027 210890392817899578830598041)
            ·
              refine ⟨158167794613424684122948531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 210890392817899578830598041 158167794613424684122948531)
              ·
                refine ⟨237251691920137026184422797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158167794613424684122948531 237251691920137026184422797)
                ·
                  refine ⟨88969384470051384819158549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 237251691920137026184422797 88969384470051384819158549)
                  ·
                    refine ⟨4170439897033658663398057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 88969384470051384819158549 4170439897033658663398057)
                    ·
                      refine ⟨3127829922775243997548543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4170439897033658663398057 3127829922775243997548543)
                      ·
                        rfl

theorem cell23_6091427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 6, 2].length) (baseStart_6091427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091427 prefixEnd_6091427 := by exact prefixLift 6091427
  have htrace : WordTrace (prefixWord ++ tailWord_6091427) baseStart_6091427 baseEnd_6091427 := by
    simpa [prefixWord, tailWord_6091427, baseEnd_6091427] using wordTrace_append hprefix tailTrace_6091427
  have hstable : (prefixWord ++ tailWord_6091427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091427).length < 2 ^ (prefixWord ++ tailWord_6091427).sum := by decide
  have hdescent : baseEnd_6091427 < baseStart_6091427 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091440 : List Nat := [2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 6]
def baseStart_6091440 : Nat := 118140960795 + 6091440 * 2 ^ 59
def prefixEnd_6091440 : Nat := 4983230072969 + 3 ^ 40 * 6091440 * 2
def baseEnd_6091440 : Nat := 3127836598023752446685983

theorem tailTrace_6091440 : CollatzResearch.WordTrace tailWord_6091440 prefixEnd_6091440 3127836598023752446685983 := by
  unfold tailWord_6091440
  simp only [CollatzResearch.WordTrace]
  refine ⟨111086534525880344985899887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148115379367840459981199849 111086534525880344985899887)
  ·
    refine ⟨166629801788820517478849831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111086534525880344985899887 166629801788820517478849831)
    ·
      refine ⟨249944702683230776218274747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166629801788820517478849831 249944702683230776218274747)
      ·
        refine ⟨374917054024846164327412121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249944702683230776218274747 374917054024846164327412121)
        ·
          refine ⟨281187790518634623245559091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374917054024846164327412121 281187790518634623245559091)
          ·
            refine ⟨421781685777951934868338637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281187790518634623245559091 421781685777951934868338637)
            ·
              refine ⟨158168132166731975575626989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 421781685777951934868338637 158168132166731975575626989)
              ·
                refine ⟨59313049562524490840860121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158168132166731975575626989 59313049562524490840860121)
                ·
                  refine ⟨44484787171893368130645091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59313049562524490840860121 44484787171893368130645091)
                  ·
                    refine ⟨66727180757840052195967637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44484787171893368130645091 66727180757840052195967637)
                    ·
                      refine ⟨3127836598023752446685983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66727180757840052195967637 3127836598023752446685983)
                      ·
                        rfl

theorem cell23_6091440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 6].length) (baseStart_6091440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091440 prefixEnd_6091440 := by exact prefixLift 6091440
  have htrace : WordTrace (prefixWord ++ tailWord_6091440) baseStart_6091440 baseEnd_6091440 := by
    simpa [prefixWord, tailWord_6091440, baseEnd_6091440] using wordTrace_append hprefix tailTrace_6091440
  have hstable : (prefixWord ++ tailWord_6091440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091440).length < 2 ^ (prefixWord ++ tailWord_6091440).sum := by decide
  have hdescent : baseEnd_6091440 < baseStart_6091440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091454 : List Nat := [4, 2, 1, 1, 2, 1, 2, 3, 3, 4]
def baseStart_6091454 : Nat := 118140960795 + 6091454 * 2 ^ 59
def prefixEnd_6091454 : Nat := 4983230072969 + 3 ^ 40 * 6091454 * 2
def baseEnd_6091454 : Nat := 1042614595584305130636973

theorem tailTrace_6091454 : CollatzResearch.WordTrace tailWord_6091454 prefixEnd_6091454 1042614595584305130636973 := by
  unfold tailWord_6091454
  simp only [CollatzResearch.WordTrace]
  refine ⟨27771697459213746295351177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148115719782473313575206277 27771697459213746295351177)
  ·
    refine ⟨20828773094410309721513383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27771697459213746295351177 20828773094410309721513383)
    ·
      refine ⟨31243159641615464582270075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20828773094410309721513383 31243159641615464582270075)
      ·
        refine ⟨46864739462423196873405113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31243159641615464582270075 46864739462423196873405113)
        ·
          refine ⟨35148554596817397655053835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46864739462423196873405113 35148554596817397655053835)
          ·
            refine ⟨52722831895226096482580753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35148554596817397655053835 52722831895226096482580753)
            ·
              refine ⟨39542123921419572361935565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52722831895226096482580753 39542123921419572361935565)
              ·
                refine ⟨14828296470532339635725837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39542123921419572361935565 14828296470532339635725837)
                ·
                  refine ⟨5560611176449627363397189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14828296470532339635725837 5560611176449627363397189)
                  ·
                    refine ⟨1042614595584305130636973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5560611176449627363397189 1042614595584305130636973)
                    ·
                      rfl

theorem cell23_6091454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_6091454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091454 prefixEnd_6091454 := by exact prefixLift 6091454
  have htrace : WordTrace (prefixWord ++ tailWord_6091454) baseStart_6091454 baseEnd_6091454 := by
    simpa [prefixWord, tailWord_6091454, baseEnd_6091454] using wordTrace_append hprefix tailTrace_6091454
  have hstable : (prefixWord ++ tailWord_6091454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091454).length < 2 ^ (prefixWord ++ tailWord_6091454).sum := by decide
  have hdescent : baseEnd_6091454 < baseStart_6091454 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091504 : List Nat := [2, 1, 1, 1, 3, 1, 4, 1, 4, 3, 2]
def baseStart_6091504 : Nat := 118140960795 + 6091504 * 2 ^ 59
def prefixEnd_6091504 : Nat := 4983230072969 + 3 ^ 40 * 6091504 * 2
def baseEnd_6091504 : Nat := 3127869460785640196285689

theorem tailTrace_6091504 : CollatzResearch.WordTrace tailWord_6091504 prefixEnd_6091504 3127869460785640196285689 := by
  unfold tailWord_6091504
  simp only [CollatzResearch.WordTrace]
  refine ⟨111087701661764414451064783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148116935549019219268086377 111087701661764414451064783)
  ·
    refine ⟨166631552492646621676597175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111087701661764414451064783 166631552492646621676597175)
    ·
      refine ⟨249947328738969932514895763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166631552492646621676597175 249947328738969932514895763)
      ·
        refine ⟨374920993108454898772343645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249947328738969932514895763 374920993108454898772343645)
        ·
          refine ⟨140595372415670587039628867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 374920993108454898772343645 140595372415670587039628867)
          ·
            refine ⟨210893058623505880559443301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140595372415670587039628867 210893058623505880559443301)
            ·
              refine ⟨39542448491907352604895619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 210893058623505880559443301 39542448491907352604895619)
              ·
                refine ⟨59313672737861028907343429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39542448491907352604895619 59313672737861028907343429)
                ·
                  refine ⟨11121313638348942920126893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59313672737861028907343429 11121313638348942920126893)
                  ·
                    refine ⟨4170492614380853595047585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11121313638348942920126893 4170492614380853595047585)
                    ·
                      refine ⟨3127869460785640196285689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4170492614380853595047585 3127869460785640196285689)
                      ·
                        rfl

theorem cell23_6091504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 4, 3, 2].length) (baseStart_6091504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091504 prefixEnd_6091504 := by exact prefixLift 6091504
  have htrace : WordTrace (prefixWord ++ tailWord_6091504) baseStart_6091504 baseEnd_6091504 := by
    simpa [prefixWord, tailWord_6091504, baseEnd_6091504] using wordTrace_append hprefix tailTrace_6091504
  have hstable : (prefixWord ++ tailWord_6091504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091504).length < 2 ^ (prefixWord ++ tailWord_6091504).sum := by decide
  have hdescent : baseEnd_6091504 < baseStart_6091504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091534 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2]
def baseStart_6091534 : Nat := 118140960795 + 6091534 * 2 ^ 59
def prefixEnd_6091534 : Nat := 4983230072969 + 3 ^ 40 * 6091534 * 2
def baseEnd_6091534 : Nat := 3127884865205275078910551

theorem tailTrace_6091534 : CollatzResearch.WordTrace tailWord_6091534 prefixEnd_6091534 3127884865205275078910551 := by
  unfold tailWord_6091534
  simp only [CollatzResearch.WordTrace]
  refine ⟨27772062189177518003215207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148117665008946762683814437 27772062189177518003215207)
  ·
    refine ⟨41658093283766277004822811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27772062189177518003215207 41658093283766277004822811)
    ·
      refine ⟨62487139925649415507234217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41658093283766277004822811 62487139925649415507234217)
      ·
        refine ⟨46865354944237061630425663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62487139925649415507234217 46865354944237061630425663)
        ·
          refine ⟨70298032416355592445638495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46865354944237061630425663 70298032416355592445638495)
          ·
            refine ⟨105447048624533388668457743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70298032416355592445638495 105447048624533388668457743)
            ·
              refine ⟨158170572936800083002686615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105447048624533388668457743 158170572936800083002686615)
              ·
                refine ⟨237255859405200124504029923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158170572936800083002686615 237255859405200124504029923)
                ·
                  refine ⟨355883789107800186756044885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 237255859405200124504029923 355883789107800186756044885)
                  ·
                    refine ⟨4170513153607033438547401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 355883789107800186756044885 4170513153607033438547401)
                    ·
                      refine ⟨3127884865205275078910551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4170513153607033438547401 3127884865205275078910551)
                      ·
                        rfl

theorem cell23_6091534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_6091534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091534 prefixEnd_6091534 := by exact prefixLift 6091534
  have htrace : WordTrace (prefixWord ++ tailWord_6091534) baseStart_6091534 baseEnd_6091534 := by
    simpa [prefixWord, tailWord_6091534, baseEnd_6091534] using wordTrace_append hprefix tailTrace_6091534
  have hstable : (prefixWord ++ tailWord_6091534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091534).length < 2 ^ (prefixWord ++ tailWord_6091534).sum := by decide
  have hdescent : baseEnd_6091534 < baseStart_6091534 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091554 : List Nat := [3, 3, 1, 1, 2, 2, 1, 3, 1, 1, 5]
def baseStart_6091554 : Nat := 118140960795 + 6091554 * 2 ^ 59
def prefixEnd_6091554 : Nat := 4983230072969 + 3 ^ 40 * 6091554 * 2
def baseEnd_6091554 : Nat := 3127895134818365000660459

theorem tailTrace_6091554 : CollatzResearch.WordTrace tailWord_6091554 prefixEnd_6091554 3127895134818365000660459 := by
  unfold tailWord_6091554
  simp only [CollatzResearch.WordTrace]
  refine ⟨55544306743336921860362429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148118151315565124960966477 55544306743336921860362429)
  ·
    refine ⟨20829115028751345697635911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55544306743336921860362429 20829115028751345697635911)
    ·
      refine ⟨31243672543127018546453867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20829115028751345697635911 31243672543127018546453867)
      ·
        refine ⟨46865508814690527819680801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31243672543127018546453867 46865508814690527819680801)
        ·
          refine ⟨35149131611017895864760601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46865508814690527819680801 35149131611017895864760601)
          ·
            refine ⟨26361848708263421898570451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35149131611017895864760601 26361848708263421898570451)
            ·
              refine ⟨39542773062395132847855677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26361848708263421898570451 39542773062395132847855677)
              ·
                refine ⟨14828539898398174817945879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39542773062395132847855677 14828539898398174817945879)
                ·
                  refine ⟨22242809847597262226918819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14828539898398174817945879 22242809847597262226918819)
                  ·
                    refine ⟨33364214771395893340378229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22242809847597262226918819 33364214771395893340378229)
                    ·
                      refine ⟨3127895134818365000660459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33364214771395893340378229 3127895134818365000660459)
                      ·
                        rfl

theorem cell23_6091554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_6091554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091554 prefixEnd_6091554 := by exact prefixLift 6091554
  have htrace : WordTrace (prefixWord ++ tailWord_6091554) baseStart_6091554 baseEnd_6091554 := by
    simpa [prefixWord, tailWord_6091554, baseEnd_6091554] using wordTrace_append hprefix tailTrace_6091554
  have hstable : (prefixWord ++ tailWord_6091554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091554).length < 2 ^ (prefixWord ++ tailWord_6091554).sum := by decide
  have hdescent : baseEnd_6091554 < baseStart_6091554 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091562 : List Nat := [3, 1, 4, 3, 2, 1, 1, 1, 3, 1, 3]
def baseStart_6091562 : Nat := 118140960795 + 6091562 * 2 ^ 59
def prefixEnd_6091562 : Nat := 4983230072969 + 3 ^ 40 * 6091562 * 2
def baseEnd_6091562 : Nat := 3127899242663600969360423

theorem tailTrace_6091562 : CollatzResearch.WordTrace tailWord_6091562 prefixEnd_6091562 3127899242663600969360423 := by
  unfold tailWord_6091562
  simp only [CollatzResearch.WordTrace]
  refine ⟨55544379689329676201935235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148118345838212469871827293 55544379689329676201935235)
  ·
    refine ⟨83316569533994514302902853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55544379689329676201935235 83316569533994514302902853)
    ·
      refine ⟨15621856787623971431794285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83316569533994514302902853 15621856787623971431794285)
      ·
        refine ⟨5858196295358989286922857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15621856787623971431794285 5858196295358989286922857)
        ·
          refine ⟨4393647221519241965192143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5858196295358989286922857 4393647221519241965192143)
          ·
            refine ⟨6590470832278862947788215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4393647221519241965192143 6590470832278862947788215)
            ·
              refine ⟨9885706248418294421682323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6590470832278862947788215 9885706248418294421682323)
              ·
                refine ⟨14828559372627441632523485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9885706248418294421682323 14828559372627441632523485)
                ·
                  refine ⟨5560709764735290612196307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14828559372627441632523485 5560709764735290612196307)
                  ·
                    refine ⟨8341064647102935918294461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5560709764735290612196307 8341064647102935918294461)
                    ·
                      refine ⟨3127899242663600969360423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8341064647102935918294461 3127899242663600969360423)
                      ·
                        rfl

theorem cell23_6091562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_6091562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091562 prefixEnd_6091562 := by exact prefixLift 6091562
  have htrace : WordTrace (prefixWord ++ tailWord_6091562) baseStart_6091562 baseEnd_6091562 := by
    simpa [prefixWord, tailWord_6091562, baseEnd_6091562] using wordTrace_append hprefix tailTrace_6091562
  have hstable : (prefixWord ++ tailWord_6091562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091562).length < 2 ^ (prefixWord ++ tailWord_6091562).sum := by decide
  have hdescent : baseEnd_6091562 < baseStart_6091562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091567 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 2, 7, 3]
def baseStart_6091567 : Nat := 118140960795 + 6091567 * 2 ^ 59
def prefixEnd_6091567 : Nat := 4983230072969 + 3 ^ 40 * 6091567 * 2
def baseEnd_6091567 : Nat := 3127901810066873449797899

theorem tailTrace_6091567 : CollatzResearch.WordTrace tailWord_6091567 prefixEnd_6091567 3127901810066873449797899 := by
  unfold tailWord_6091567
  simp only [CollatzResearch.WordTrace]
  refine ⟨222177701122300590661672955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148118467414867060441115303 222177701122300590661672955)
  ·
    refine ⟨333266551683450885992509433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222177701122300590661672955 333266551683450885992509433)
    ·
      refine ⟨249949913762588164494382075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333266551683450885992509433 249949913762588164494382075)
      ·
        refine ⟨374924870643882246741573113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249949913762588164494382075 374924870643882246741573113)
        ·
          refine ⟨281193652982911685056179835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374924870643882246741573113 281193652982911685056179835)
          ·
            refine ⟨421790479474367527584269753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281193652982911685056179835 421790479474367527584269753)
            ·
              refine ⟨316342859605775645688202315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 421790479474367527584269753 316342859605775645688202315)
              ·
                refine ⟨474514289408663468532303473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 316342859605775645688202315 474514289408663468532303473)
                ·
                  refine ⟨355885717056497601399227605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 474514289408663468532303473 355885717056497601399227605)
                  ·
                    refine ⟨8341071493511662532794397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 355885717056497601399227605 8341071493511662532794397)
                    ·
                      refine ⟨3127901810066873449797899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8341071493511662532794397 3127901810066873449797899)
                      ·
                        rfl

theorem cell23_6091567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 7, 3].length) (baseStart_6091567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091567 prefixEnd_6091567 := by exact prefixLift 6091567
  have htrace : WordTrace (prefixWord ++ tailWord_6091567) baseStart_6091567 baseEnd_6091567 := by
    simpa [prefixWord, tailWord_6091567, baseEnd_6091567] using wordTrace_append hprefix tailTrace_6091567
  have hstable : (prefixWord ++ tailWord_6091567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091567).length < 2 ^ (prefixWord ++ tailWord_6091567).sum := by decide
  have hdescent : baseEnd_6091567 < baseStart_6091567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091568 : List Nat := [2, 1, 1, 1, 2, 2, 1, 8, 1, 2, 2]
def baseStart_6091568 : Nat := 118140960795 + 6091568 * 2 ^ 59
def prefixEnd_6091568 : Nat := 4983230072969 + 3 ^ 40 * 6091568 * 2
def baseEnd_6091568 : Nat := 3127902323547527945885395

theorem tailTrace_6091568 : CollatzResearch.WordTrace tailWord_6091568 prefixEnd_6091568 3127902323547527945885395 := by
  unfold tailWord_6091568
  simp only [CollatzResearch.WordTrace]
  refine ⟨111088868797648483916229679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148118491730197978554972905 111088868797648483916229679)
  ·
    refine ⟨166633303196472725874344519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111088868797648483916229679 166633303196472725874344519)
    ·
      refine ⟨249949954794709088811516779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166633303196472725874344519 249949954794709088811516779)
      ·
        refine ⟨374924932192063633217275169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249949954794709088811516779 374924932192063633217275169)
        ·
          refine ⟨281193699144047724912956377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 374924932192063633217275169 281193699144047724912956377)
          ·
            refine ⟨210895274358035793684717283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281193699144047724912956377 210895274358035793684717283)
            ·
              refine ⟨316342911537053690527075925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210895274358035793684717283 316342911537053690527075925)
              ·
                refine ⟨3707143494574847935864171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 316342911537053690527075925 3707143494574847935864171)
                ·
                  refine ⟨5560715241862271903796257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3707143494574847935864171 5560715241862271903796257)
                  ·
                    refine ⟨4170536431396703927847193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5560715241862271903796257 4170536431396703927847193)
                    ·
                      refine ⟨3127902323547527945885395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4170536431396703927847193 3127902323547527945885395)
                      ·
                        rfl

theorem cell23_6091568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 8, 1, 2, 2].length) (baseStart_6091568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091568 prefixEnd_6091568 := by exact prefixLift 6091568
  have htrace : WordTrace (prefixWord ++ tailWord_6091568) baseStart_6091568 baseEnd_6091568 := by
    simpa [prefixWord, tailWord_6091568, baseEnd_6091568] using wordTrace_append hprefix tailTrace_6091568
  have hstable : (prefixWord ++ tailWord_6091568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091568).length < 2 ^ (prefixWord ++ tailWord_6091568).sum := by decide
  have hdescent : baseEnd_6091568 < baseStart_6091568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091585 : List Nat := [1, 2, 5, 3, 1, 2, 1, 2, 1, 1, 4]
def baseStart_6091585 : Nat := 118140960795 + 6091585 * 2 ^ 59
def prefixEnd_6091585 : Nat := 4983230072969 + 3 ^ 40 * 6091585 * 2
def baseEnd_6091585 : Nat := 3127911052718654379372817

theorem tailTrace_6091585 : CollatzResearch.WordTrace tailWord_6091585 prefixEnd_6091585 3127911052718654379372817 := by
  unfold tailWord_6091585
  simp only [CollatzResearch.WordTrace]
  refine ⟨222178357636235379735828209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148118905090823586490552139 222178357636235379735828209)
  ·
    refine ⟨166633768227176534801871157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222178357636235379735828209 166633768227176534801871157)
    ·
      refine ⟨15621915771297800137675421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 166633768227176534801871157 15621915771297800137675421)
      ·
        refine ⟨5858218414236675051628283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15621915771297800137675421 5858218414236675051628283)
        ·
          refine ⟨8787327621355012577442425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5858218414236675051628283 8787327621355012577442425)
          ·
            refine ⟨6590495716016259433081819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8787327621355012577442425 6590495716016259433081819)
            ·
              refine ⟨9885743574024389149622729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6590495716016259433081819 9885743574024389149622729)
              ·
                refine ⟨7414307680518291862217047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9885743574024389149622729 7414307680518291862217047)
                ·
                  refine ⟨11121461520777437793325571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7414307680518291862217047 11121461520777437793325571)
                  ·
                    refine ⟨16682192281166156689988357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11121461520777437793325571 16682192281166156689988357)
                    ·
                      refine ⟨3127911052718654379372817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16682192281166156689988357 3127911052718654379372817)
                      ·
                        rfl

theorem cell23_6091585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_6091585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091585 prefixEnd_6091585 := by exact prefixLift 6091585
  have htrace : WordTrace (prefixWord ++ tailWord_6091585) baseStart_6091585 baseEnd_6091585 := by
    simpa [prefixWord, tailWord_6091585, baseEnd_6091585] using wordTrace_append hprefix tailTrace_6091585
  have hstable : (prefixWord ++ tailWord_6091585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091585).length < 2 ^ (prefixWord ++ tailWord_6091585).sum := by decide
  have hdescent : baseEnd_6091585 < baseStart_6091585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6091601 : List Nat := [1, 2, 2, 1, 6, 1, 1, 2, 1, 3, 3]
def baseStart_6091601 : Nat := 118140960795 + 6091601 * 2 ^ 59
def prefixEnd_6091601 : Nat := 4983230072969 + 3 ^ 40 * 6091601 * 2
def baseEnd_6091601 : Nat := 3127919268409126316772743

theorem tailTrace_6091601 : CollatzResearch.WordTrace tailWord_6091601 prefixEnd_6091601 3127919268409126316772743 := by
  unfold tailWord_6091601
  simp only [CollatzResearch.WordTrace]
  refine ⟨222178941204177414468410657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148119294136118276312273771 222178941204177414468410657)
  ·
    refine ⟨166634205903133060851307993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222178941204177414468410657 166634205903133060851307993)
    ·
      refine ⟨124975654427349795638480995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166634205903133060851307993 124975654427349795638480995)
      ·
        refine ⟨187463481641024693457721493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124975654427349795638480995 187463481641024693457721493)
        ·
          refine ⟨8787350701923032505830695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 187463481641024693457721493 8787350701923032505830695)
          ·
            refine ⟨13181026052884548758746043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8787350701923032505830695 13181026052884548758746043)
            ·
              refine ⟨19771539079326823138119065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13181026052884548758746043 19771539079326823138119065)
              ·
                refine ⟨14828654309495117353589299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19771539079326823138119065 14828654309495117353589299)
                ·
                  refine ⟨22242981464242676030383949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14828654309495117353589299 22242981464242676030383949)
                  ·
                    refine ⟨8341118049091003511393981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22242981464242676030383949 8341118049091003511393981)
                    ·
                      refine ⟨3127919268409126316772743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8341118049091003511393981 3127919268409126316772743)
                      ·
                        rfl

theorem cell23_6091601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 3, 3].length) (baseStart_6091601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6091601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6091601 prefixEnd_6091601 := by exact prefixLift 6091601
  have htrace : WordTrace (prefixWord ++ tailWord_6091601) baseStart_6091601 baseEnd_6091601 := by
    simpa [prefixWord, tailWord_6091601, baseEnd_6091601] using wordTrace_append hprefix tailTrace_6091601
  have hstable : (prefixWord ++ tailWord_6091601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6091601).length < 2 ^ (prefixWord ++ tailWord_6091601).sum := by decide
  have hdescent : baseEnd_6091601 < baseStart_6091601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6091601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
