import V185TrunkScan22Chunk008

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_80125 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 4, 6]
def baseStart_80125 : Nat := 118140960795 + 80125 * 2 ^ 59
def prefixEnd_80125 : Nat := 4983230072969 + 3 ^ 40 * 80125 * 2
def baseEnd_80125 : Nat := 27428424961069496179345

theorem tailTrace_80125 : CollatzResearch.WordTrace tailWord_80125 prefixEnd_80125 27428424961069496179345 := by
  unfold tailWord_80125
  simp only [CollatzResearch.WordTrace]
  refine ⟨2922398834728284105649829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1948265889818856070433219 2922398834728284105649829)
  ·
    refine ⟨547949781511553269809343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2922398834728284105649829 547949781511553269809343)
    ·
      refine ⟨821924672267329904714015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 547949781511553269809343 821924672267329904714015)
      ·
        refine ⟨1232887008400994857071023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 821924672267329904714015 1232887008400994857071023)
        ·
          refine ⟨1849330512601492285606535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1232887008400994857071023 1849330512601492285606535)
          ·
            refine ⟨2773995768902238428409803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1849330512601492285606535 2773995768902238428409803)
            ·
              refine ⟨4160993653353357642614705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2773995768902238428409803 4160993653353357642614705)
              ·
                refine ⟨3120745240015018231961029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4160993653353357642614705 3120745240015018231961029)
                ·
                  refine ⟨585139732502815918492693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3120745240015018231961029 585139732502815918492693)
                  ·
                    refine ⟨27428424961069496179345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 585139732502815918492693 27428424961069496179345)
                    ·
                      rfl

theorem cell22_80125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_80125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_80125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_80125 prefixEnd_80125 := by exact prefixLift 80125
  have htrace : WordTrace (prefixWord ++ tailWord_80125) baseStart_80125 baseEnd_80125 := by
    simpa [prefixWord, tailWord_80125, baseEnd_80125] using wordTrace_append hprefix tailTrace_80125
  have hstable : (prefixWord ++ tailWord_80125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80125).length < 2 ^ (prefixWord ++ tailWord_80125).sum := by decide
  have hdescent : baseEnd_80125 < baseStart_80125 := by decide
  rcases family_descends (prefixWord ++ tailWord_80125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80135 : List Nat := [1, 1, 4, 5, 2, 1, 2, 2, 4]
def baseStart_80135 : Nat := 118140960795 + 80135 * 2 ^ 59
def prefixEnd_80135 : Nat := 4983230072969 + 3 ^ 40 * 80135 * 2
def baseEnd_80135 : Nat := 9143949388477601143105

theorem tailTrace_80135 : CollatzResearch.WordTrace tailWord_80135 prefixEnd_80135 9143949388477601143105 := by
  unfold tailWord_80135
  simp only [CollatzResearch.WordTrace]
  refine ⟨2922763564692055813513859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1948509043128037209009239 2922763564692055813513859)
  ·
    refine ⟨4384145347038083720270789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2922763564692055813513859 4384145347038083720270789)
    ·
      refine ⟨822027252569640697550773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4384145347038083720270789 822027252569640697550773)
      ·
        refine ⟨77065054928403815395385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 822027252569640697550773 77065054928403815395385)
        ·
          refine ⟨57798791196302861546539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77065054928403815395385 57798791196302861546539)
          ·
            refine ⟨86698186794454292319809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57798791196302861546539 86698186794454292319809)
            ·
              refine ⟨65023640095840719239857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86698186794454292319809 65023640095840719239857)
              ·
                refine ⟨48767730071880539429893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65023640095840719239857 48767730071880539429893)
                ·
                  refine ⟨9143949388477601143105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48767730071880539429893 9143949388477601143105)
                  ·
                    rfl

theorem cell22_80135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 2, 4].length) (baseStart_80135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_80135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_80135 prefixEnd_80135 := by exact prefixLift 80135
  have htrace : WordTrace (prefixWord ++ tailWord_80135) baseStart_80135 baseEnd_80135 := by
    simpa [prefixWord, tailWord_80135, baseEnd_80135] using wordTrace_append hprefix tailTrace_80135
  have hstable : (prefixWord ++ tailWord_80135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80135).length < 2 ^ (prefixWord ++ tailWord_80135).sum := by decide
  have hdescent : baseEnd_80135 < baseStart_80135 := by decide
  rcases family_descends (prefixWord ++ tailWord_80135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80155 : List Nat := [1, 1, 1, 1, 1, 1, 7, 1, 1, 7]
def baseStart_80155 : Nat := 118140960795 + 80155 * 2 ^ 59
def prefixEnd_80155 : Nat := 4983230072969 + 3 ^ 40 * 80155 * 2
def baseEnd_80155 : Nat := 27438694574159417929253

theorem tailTrace_80155 : CollatzResearch.WordTrace tailWord_80155 prefixEnd_80155 27438694574159417929253 := by
  unfold tailWord_80155
  simp only [CollatzResearch.WordTrace]
  refine ⟨2923493024619599229241919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1948995349746399486161279 2923493024619599229241919)
  ·
    refine ⟨4385239536929398843862879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2923493024619599229241919 4385239536929398843862879)
    ·
      refine ⟨6577859305394098265794319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4385239536929398843862879 6577859305394098265794319)
      ·
        refine ⟨9866788958091147398691479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6577859305394098265794319 9866788958091147398691479)
        ·
          refine ⟨14800183437136721098037219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9866788958091147398691479 14800183437136721098037219)
          ·
            refine ⟨22200275155705081647055829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14800183437136721098037219 22200275155705081647055829)
            ·
              refine ⟨520318948961837851102871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 22200275155705081647055829 520318948961837851102871)
              ·
                refine ⟨780478423442756776654307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 520318948961837851102871 780478423442756776654307)
                ·
                  refine ⟨1170717635164135164981461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 780478423442756776654307 1170717635164135164981461)
                  ·
                    refine ⟨27438694574159417929253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1170717635164135164981461 27438694574159417929253)
                    ·
                      rfl

theorem cell22_80155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 7].length) (baseStart_80155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_80155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_80155 prefixEnd_80155 := by exact prefixLift 80155
  have htrace : WordTrace (prefixWord ++ tailWord_80155) baseStart_80155 baseEnd_80155 := by
    simpa [prefixWord, tailWord_80155, baseEnd_80155] using wordTrace_append hprefix tailTrace_80155
  have hstable : (prefixWord ++ tailWord_80155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80155).length < 2 ^ (prefixWord ++ tailWord_80155).sum := by decide
  have hdescent : baseEnd_80155 < baseStart_80155 := by decide
  rcases family_descends (prefixWord ++ tailWord_80155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80178 : List Nat := [3, 2, 1, 1, 5, 1, 2, 3, 1, 3]
def baseStart_80178 : Nat := 118140960795 + 80178 * 2 ^ 59
def prefixEnd_80178 : Nat := 4983230072969 + 3 ^ 40 * 80178 * 2
def baseEnd_80178 : Nat := 27446567944195024604183

theorem tailTrace_80178 : CollatzResearch.WordTrace tailWord_80178 prefixEnd_80178 27446567944195024604183 := by
  unfold tailWord_80178
  simp only [CollatzResearch.WordTrace]
  refine ⟨731082975884068539332297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1949554602357516104886125 731082975884068539332297)
  ·
    refine ⟨548312231913051404499223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 731082975884068539332297 548312231913051404499223)
    ·
      refine ⟨822468347869577106748835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 548312231913051404499223 822468347869577106748835)
      ·
        refine ⟨1233702521804365660123253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 822468347869577106748835 1233702521804365660123253)
        ·
          refine ⟨115659611419159280636555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1233702521804365660123253 115659611419159280636555)
          ·
            refine ⟨173489417128738920954833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115659611419159280636555 173489417128738920954833)
            ·
              refine ⟨130117062846554190716125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173489417128738920954833 130117062846554190716125)
              ·
                refine ⟨48793898567457821518547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130117062846554190716125 48793898567457821518547)
                ·
                  refine ⟨73190847851186732277821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48793898567457821518547 73190847851186732277821)
                  ·
                    refine ⟨27446567944195024604183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73190847851186732277821 27446567944195024604183)
                    ·
                      rfl

theorem cell22_80178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 3, 1, 3].length) (baseStart_80178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_80178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_80178 prefixEnd_80178 := by exact prefixLift 80178
  have htrace : WordTrace (prefixWord ++ tailWord_80178) baseStart_80178 baseEnd_80178 := by
    simpa [prefixWord, tailWord_80178, baseEnd_80178] using wordTrace_append hprefix tailTrace_80178
  have hstable : (prefixWord ++ tailWord_80178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80178).length < 2 ^ (prefixWord ++ tailWord_80178).sum := by decide
  have hdescent : baseEnd_80178 < baseStart_80178 := by decide
  rcases family_descends (prefixWord ++ tailWord_80178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80268 : List Nat := [2, 2, 1, 2, 1, 6, 2, 1, 2, 3]
def baseStart_80268 : Nat := 118140960795 + 80268 * 2 ^ 59
def prefixEnd_80268 : Nat := 4983230072969 + 3 ^ 40 * 80268 * 2
def baseEnd_80268 : Nat := 27477376783464789853907

theorem tailTrace_80268 : CollatzResearch.WordTrace tailWord_80268 prefixEnd_80268 27477376783464789853907 := by
  unfold tailWord_80268
  simp only [CollatzResearch.WordTrace]
  refine ⟨1463807236605109764052729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1951742982140146352070305 1463807236605109764052729)
  ·
    refine ⟨1097855427453832323039547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1463807236605109764052729 1097855427453832323039547)
    ·
      refine ⟨1646783141180748484559321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1097855427453832323039547 1646783141180748484559321)
      ·
        refine ⟨1235087355885561363419491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1646783141180748484559321 1235087355885561363419491)
        ·
          refine ⟨1852631033828342045129237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1235087355885561363419491 1852631033828342045129237)
          ·
            refine ⟨86842079710703533365433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1852631033828342045129237 86842079710703533365433)
            ·
              refine ⟨65131559783027650024075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86842079710703533365433 65131559783027650024075)
              ·
                refine ⟨97697339674541475036113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65131559783027650024075 97697339674541475036113)
                ·
                  refine ⟨73273004755906106277085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97697339674541475036113 73273004755906106277085)
                  ·
                    refine ⟨27477376783464789853907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73273004755906106277085 27477376783464789853907)
                    ·
                      rfl

theorem cell22_80268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 2, 3].length) (baseStart_80268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_80268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_80268 prefixEnd_80268 := by exact prefixLift 80268
  have htrace : WordTrace (prefixWord ++ tailWord_80268) baseStart_80268 baseEnd_80268 := by
    simpa [prefixWord, tailWord_80268, baseEnd_80268] using wordTrace_append hprefix tailTrace_80268
  have hstable : (prefixWord ++ tailWord_80268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80268).length < 2 ^ (prefixWord ++ tailWord_80268).sum := by decide
  have hdescent : baseEnd_80268 < baseStart_80268 := by decide
  rcases family_descends (prefixWord ++ tailWord_80268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80279 : List Nat := [1, 1, 3, 3, 1, 1, 2, 4, 3, 3]
def baseStart_80279 : Nat := 118140960795 + 80279 * 2 ^ 59
def prefixEnd_80279 : Nat := 4983230072969 + 3 ^ 40 * 80279 * 2
def baseEnd_80279 : Nat := 27481142308264427828873

theorem tailTrace_80279 : CollatzResearch.WordTrace tailWord_80279 prefixEnd_80279 27481142308264427828873 := by
  unfold tailWord_80279
  simp only [CollatzResearch.WordTrace]
  refine ⟨2928015676170368406755891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1952010450780245604503927 2928015676170368406755891)
  ·
    refine ⟨4392023514255552610133837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2928015676170368406755891 4392023514255552610133837)
    ·
      refine ⟨1647008817845832228800189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4392023514255552610133837 1647008817845832228800189)
      ·
        refine ⟨617628306692187085800071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1647008817845832228800189 617628306692187085800071)
        ·
          refine ⟨926442460038280628700107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 617628306692187085800071 926442460038280628700107)
          ·
            refine ⟨1389663690057420943050161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 926442460038280628700107 1389663690057420943050161)
            ·
              refine ⟨1042247767543065707287621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1389663690057420943050161 1042247767543065707287621)
              ·
                refine ⟨195421456414324820116429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1042247767543065707287621 195421456414324820116429)
                ·
                  refine ⟨73283046155371807543661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 195421456414324820116429 73283046155371807543661)
                  ·
                    refine ⟨27481142308264427828873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73283046155371807543661 27481142308264427828873)
                    ·
                      rfl

theorem cell22_80279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 3, 3].length) (baseStart_80279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_80279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_80279 prefixEnd_80279 := by exact prefixLift 80279
  have htrace : WordTrace (prefixWord ++ tailWord_80279) baseStart_80279 baseEnd_80279 := by
    simpa [prefixWord, tailWord_80279, baseEnd_80279] using wordTrace_append hprefix tailTrace_80279
  have hstable : (prefixWord ++ tailWord_80279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80279).length < 2 ^ (prefixWord ++ tailWord_80279).sum := by decide
  have hdescent : baseEnd_80279 < baseStart_80279 := by decide
  rcases family_descends (prefixWord ++ tailWord_80279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80292 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 9]
def baseStart_80292 : Nat := 118140960795 + 80292 * 2 ^ 59
def prefixEnd_80292 : Nat := 4983230072969 + 3 ^ 40 * 80292 * 2
def baseEnd_80292 : Nat := 9161864157978909084611

theorem tailTrace_80292 : CollatzResearch.WordTrace tailWord_80292 prefixEnd_80292 9161864157978909084611 := by
  unfold tailWord_80292
  simp only [CollatzResearch.WordTrace]
  refine ⟨1464244912561635813489565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1952326550082181084652753 1464244912561635813489565)
  ·
    refine ⟨549091842210613430058587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1464244912561635813489565 549091842210613430058587)
    ·
      refine ⟨823637763315920145087881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 549091842210613430058587 823637763315920145087881)
      ·
        refine ⟨617728322486940108815911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 823637763315920145087881 617728322486940108815911)
        ·
          refine ⟨926592483730410163223867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 617728322486940108815911 926592483730410163223867)
          ·
            refine ⟨1389888725595615244835801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 926592483730410163223867 1389888725595615244835801)
            ·
              refine ⟨1042416544196711433626851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1389888725595615244835801 1042416544196711433626851)
              ·
                refine ⟨1563624816295067150440277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1042416544196711433626851 1563624816295067150440277)
                ·
                  refine ⟨9161864157978909084611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1563624816295067150440277 9161864157978909084611)
                  ·
                    rfl

theorem cell22_80292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_80292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_80292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_80292 prefixEnd_80292 := by exact prefixLift 80292
  have htrace : WordTrace (prefixWord ++ tailWord_80292) baseStart_80292 baseEnd_80292 := by
    simpa [prefixWord, tailWord_80292, baseEnd_80292] using wordTrace_append hprefix tailTrace_80292
  have hstable : (prefixWord ++ tailWord_80292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80292).length < 2 ^ (prefixWord ++ tailWord_80292).sum := by decide
  have hdescent : baseEnd_80292 < baseStart_80292 := by decide
  rcases family_descends (prefixWord ++ tailWord_80292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80298 : List Nat := [3, 1, 6, 1, 2, 9]
def baseStart_80298 : Nat := 118140960795 + 80298 * 2 ^ 59
def prefixEnd_80298 : Nat := 4983230072969 + 3 ^ 40 * 80298 * 2
def baseEnd_80298 : Nat := 339353659216724834615

theorem tailTrace_80298 : CollatzResearch.WordTrace tailWord_80298 prefixEnd_80298 339353659216724834615 := by
  unfold tailWord_80298
  simp only [CollatzResearch.WordTrace]
  refine ⟨732177165775383662924387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1952472442067689767798365 732177165775383662924387)
  ·
    refine ⟨1098265748663075494386581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 732177165775383662924387 1098265748663075494386581)
    ·
      refine ⟨51481206968581663799371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1098265748663075494386581 51481206968581663799371)
      ·
        refine ⟨77221810452872495699057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51481206968581663799371 77221810452872495699057)
        ·
          refine ⟨57916357839654371774293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77221810452872495699057 57916357839654371774293)
          ·
            refine ⟨339353659216724834615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 57916357839654371774293 339353659216724834615)
            ·
              rfl

theorem cell22_80298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 9].length) (baseStart_80298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_80298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_80298 prefixEnd_80298 := by exact prefixLift 80298
  have htrace : WordTrace (prefixWord ++ tailWord_80298) baseStart_80298 baseEnd_80298 := by
    simpa [prefixWord, tailWord_80298, baseEnd_80298] using wordTrace_append hprefix tailTrace_80298
  have hstable : (prefixWord ++ tailWord_80298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80298).length < 2 ^ (prefixWord ++ tailWord_80298).sum := by decide
  have hdescent : baseEnd_80298 < baseStart_80298 := by decide
  rcases family_descends (prefixWord ++ tailWord_80298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80313 : List Nat := [1, 2, 1, 4, 3, 2, 1, 4, 1, 3]
def baseStart_80313 : Nat := 118140960795 + 80313 * 2 ^ 59
def prefixEnd_80313 : Nat := 4983230072969 + 3 ^ 40 * 80313 * 2
def baseEnd_80313 : Nat := 27492781203099672478769

theorem tailTrace_80313 : CollatzResearch.WordTrace tailWord_80313 prefixEnd_80313 27492781203099672478769 := by
  unfold tailWord_80313
  simp only [CollatzResearch.WordTrace]
  refine ⟨2929255758047192213493593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1952837172031461475662395 2929255758047192213493593)
  ·
    refine ⟨2196941818535394160120195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2929255758047192213493593 2196941818535394160120195)
    ·
      refine ⟨3295412727803091240180293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2196941818535394160120195 3295412727803091240180293)
      ·
        refine ⟨617889886463079607533805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3295412727803091240180293 617889886463079607533805)
        ·
          refine ⟨231708707423654852825177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 617889886463079607533805 231708707423654852825177)
          ·
            refine ⟨173781530567741139618883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231708707423654852825177 173781530567741139618883)
            ·
              refine ⟨260672295851611709428325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173781530567741139618883 260672295851611709428325)
              ·
                refine ⟨48876055472177195517811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 260672295851611709428325 48876055472177195517811)
                ·
                  refine ⟨73314083208265793276717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48876055472177195517811 73314083208265793276717)
                  ·
                    refine ⟨27492781203099672478769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73314083208265793276717 27492781203099672478769)
                    ·
                      rfl

theorem cell22_80313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 4, 1, 3].length) (baseStart_80313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_80313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_80313 prefixEnd_80313 := by exact prefixLift 80313
  have htrace : WordTrace (prefixWord ++ tailWord_80313) baseStart_80313 baseEnd_80313 := by
    simpa [prefixWord, tailWord_80313, baseEnd_80313] using wordTrace_append hprefix tailTrace_80313
  have hstable : (prefixWord ++ tailWord_80313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80313).length < 2 ^ (prefixWord ++ tailWord_80313).sum := by decide
  have hdescent : baseEnd_80313 < baseStart_80313 := by decide
  rcases family_descends (prefixWord ++ tailWord_80313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80416 : List Nat := [2, 1, 1, 6, 2, 2, 8]
def baseStart_80416 : Nat := 118140960795 + 80416 * 2 ^ 59
def prefixEnd_80416 : Nat := 4983230072969 + 3 ^ 40 * 80416 * 2
def baseEnd_80416 : Nat := 1019557044742286561239

theorem tailTrace_80416 : CollatzResearch.WordTrace tailWord_80416 prefixEnd_80416 1019557044742286561239 := by
  unfold tailWord_80416
  simp only [CollatzResearch.WordTrace]
  refine ⟨1466506238337020402246551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1955341651116027202995401 1466506238337020402246551)
  ·
    refine ⟨2199759357505530603369827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1466506238337020402246551 2199759357505530603369827)
    ·
      refine ⟨3299639036258295905054741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2199759357505530603369827 3299639036258295905054741)
      ·
        refine ⟨154670579824607620549441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3299639036258295905054741 154670579824607620549441)
        ·
          refine ⟨116002934868455715412081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154670579824607620549441 116002934868455715412081)
          ·
            refine ⟨87002201151341786559061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116002934868455715412081 87002201151341786559061)
            ·
              refine ⟨1019557044742286561239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 87002201151341786559061 1019557044742286561239)
              ·
                rfl

theorem cell22_80416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 8].length) (baseStart_80416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_80416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_80416 prefixEnd_80416 := by exact prefixLift 80416
  have htrace : WordTrace (prefixWord ++ tailWord_80416) baseStart_80416 baseEnd_80416 := by
    simpa [prefixWord, tailWord_80416, baseEnd_80416] using wordTrace_append hprefix tailTrace_80416
  have hstable : (prefixWord ++ tailWord_80416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80416).length < 2 ^ (prefixWord ++ tailWord_80416).sum := by decide
  have hdescent : baseEnd_80416 < baseStart_80416 := by decide
  rcases family_descends (prefixWord ++ tailWord_80416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80452 : List Nat := [2, 3, 5, 1, 1, 1, 2, 1, 2, 4]
def baseStart_80452 : Nat := 118140960795 + 80452 * 2 ^ 59
def prefixEnd_80452 : Nat := 4983230072969 + 3 ^ 40 * 80452 * 2
def baseEnd_80452 : Nat := 27540363743749643253343

theorem tailTrace_80452 : CollatzResearch.WordTrace tailWord_80452 prefixEnd_80452 27540363743749643253343 := by
  unfold tailWord_80452
  simp only [CollatzResearch.WordTrace]
  refine ⟨1467162752271809476401805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1956217003029079301869073 1467162752271809476401805)
  ·
    refine ⟨550186032101928553650677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1467162752271809476401805 550186032101928553650677)
    ·
      refine ⟨51579940509555801904751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 550186032101928553650677 51579940509555801904751)
      ·
        refine ⟨77369910764333702857127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51579940509555801904751 77369910764333702857127)
        ·
          refine ⟨116054866146500554285691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77369910764333702857127 116054866146500554285691)
          ·
            refine ⟨174082299219750831428537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116054866146500554285691 174082299219750831428537)
            ·
              refine ⟨130561724414813123571403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174082299219750831428537 130561724414813123571403)
              ·
                refine ⟨195842586622219685357105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130561724414813123571403 195842586622219685357105)
                ·
                  refine ⟨146881939966664764017829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195842586622219685357105 146881939966664764017829)
                  ·
                    refine ⟨27540363743749643253343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 146881939966664764017829 27540363743749643253343)
                    ·
                      rfl

theorem cell22_80452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_80452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_80452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_80452 prefixEnd_80452 := by exact prefixLift 80452
  have htrace : WordTrace (prefixWord ++ tailWord_80452) baseStart_80452 baseEnd_80452 := by
    simpa [prefixWord, tailWord_80452, baseEnd_80452] using wordTrace_append hprefix tailTrace_80452
  have hstable : (prefixWord ++ tailWord_80452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80452).length < 2 ^ (prefixWord ++ tailWord_80452).sum := by decide
  have hdescent : baseEnd_80452 < baseStart_80452 := by decide
  rcases family_descends (prefixWord ++ tailWord_80452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80489 : List Nat := [1, 2, 1, 1, 1, 4, 1, 5, 6]
def baseStart_80489 : Nat := 118140960795 + 80489 * 2 ^ 59
def prefixEnd_80489 : Nat := 4983230072969 + 3 ^ 40 * 80489 * 2
def baseEnd_80489 : Nat := 9184343199964626692743

theorem tailTrace_80489 : CollatzResearch.WordTrace tailWord_80489 prefixEnd_80489 9184343199964626692743 := by
  unfold tailWord_80489
  simp only [CollatzResearch.WordTrace]
  refine ⟨2935675005409574271900521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1957116670273049514600347 2935675005409574271900521)
  ·
    refine ⟨2201756254057180703925391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2935675005409574271900521 2201756254057180703925391)
    ·
      refine ⟨3302634381085771055888087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2201756254057180703925391 3302634381085771055888087)
      ·
        refine ⟨4953951571628656583832131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3302634381085771055888087 4953951571628656583832131)
        ·
          refine ⟨7430927357442984875748197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4953951571628656583832131 7430927357442984875748197)
          ·
            refine ⟨1393298879520559664202787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7430927357442984875748197 1393298879520559664202787)
            ·
              refine ⟨2089948319280839496304181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1393298879520559664202787 2089948319280839496304181)
              ·
                refine ⟨195932654932578702778517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2089948319280839496304181 195932654932578702778517)
                ·
                  refine ⟨9184343199964626692743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 195932654932578702778517 9184343199964626692743)
                  ·
                    rfl

theorem cell22_80489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 6].length) (baseStart_80489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_80489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_80489 prefixEnd_80489 := by exact prefixLift 80489
  have htrace : WordTrace (prefixWord ++ tailWord_80489) baseStart_80489 baseEnd_80489 := by
    simpa [prefixWord, tailWord_80489, baseEnd_80489] using wordTrace_append hprefix tailTrace_80489
  have hstable : (prefixWord ++ tailWord_80489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80489).length < 2 ^ (prefixWord ++ tailWord_80489).sum := by decide
  have hdescent : baseEnd_80489 < baseStart_80489 := by decide
  rcases family_descends (prefixWord ++ tailWord_80489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80504 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 5, 5]
def baseStart_80504 : Nat := 118140960795 + 80504 * 2 ^ 59
def prefixEnd_80504 : Nat := 4983230072969 + 3 ^ 40 * 80504 * 2
def baseEnd_80504 : Nat := 27558164406438840953183

theorem tailTrace_80504 : CollatzResearch.WordTrace tailWord_80504 prefixEnd_80504 27558164406438840953183 := by
  unfold tailWord_80504
  simp only [CollatzResearch.WordTrace]
  refine ⟨1468111050177615916848283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1957481400236821222464377 1468111050177615916848283)
  ·
    refine ⟨2202166575266423875272425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1468111050177615916848283 2202166575266423875272425)
    ·
      refine ⟨1651624931449817906454319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2202166575266423875272425 1651624931449817906454319)
      ·
        refine ⟨2477437397174726859681479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1651624931449817906454319 2477437397174726859681479)
        ·
          refine ⟨3716156095762090289522219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2477437397174726859681479 3716156095762090289522219)
          ·
            refine ⟨5574234143643135434283329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3716156095762090289522219 5574234143643135434283329)
            ·
              refine ⟨4180675607732351575712497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5574234143643135434283329 4180675607732351575712497)
              ·
                refine ⟨3135506705799263681784373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4180675607732351575712497 3135506705799263681784373)
                ·
                  refine ⟨293953753668680970167285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3135506705799263681784373 293953753668680970167285)
                  ·
                    refine ⟨27558164406438840953183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 293953753668680970167285 27558164406438840953183)
                    ·
                      rfl

theorem cell22_80504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_80504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_80504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_80504 prefixEnd_80504 := by exact prefixLift 80504
  have htrace : WordTrace (prefixWord ++ tailWord_80504) baseStart_80504 baseEnd_80504 := by
    simpa [prefixWord, tailWord_80504, baseEnd_80504] using wordTrace_append hprefix tailTrace_80504
  have hstable : (prefixWord ++ tailWord_80504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80504).length < 2 ^ (prefixWord ++ tailWord_80504).sum := by decide
  have hdescent : baseEnd_80504 < baseStart_80504 := by decide
  rcases family_descends (prefixWord ++ tailWord_80504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80521 : List Nat := [1, 2, 1, 1, 4, 1, 1, 4, 4, 3]
def baseStart_80521 : Nat := 118140960795 + 80521 * 2 ^ 59
def prefixEnd_80521 : Nat := 4983230072969 + 3 ^ 40 * 80521 * 2
def baseEnd_80521 : Nat := 27563983853856463278131

theorem tailTrace_80521 : CollatzResearch.WordTrace tailWord_80521 prefixEnd_80521 27563983853856463278131 := by
  unfold tailWord_80521
  simp only [CollatzResearch.WordTrace]
  refine ⟨2936842141293643737065417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1957894760862429158043611 2936842141293643737065417)
  ·
    refine ⟨2202631605970232802799063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2936842141293643737065417 2202631605970232802799063)
    ·
      refine ⟨3303947408955349204198595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2202631605970232802799063 3303947408955349204198595)
      ·
        refine ⟨4955921113433023806297893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3303947408955349204198595 4955921113433023806297893)
        ·
          refine ⟨929235208768691963680855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4955921113433023806297893 929235208768691963680855)
          ·
            refine ⟨1393852813153037945521283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 929235208768691963680855 1393852813153037945521283)
            ·
              refine ⟨2090779219729556918281925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1393852813153037945521283 2090779219729556918281925)
              ·
                refine ⟨392021103699291922177861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2090779219729556918281925 392021103699291922177861)
                ·
                  refine ⟨73503956943617235408349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 392021103699291922177861 73503956943617235408349)
                  ·
                    refine ⟨27563983853856463278131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73503956943617235408349 27563983853856463278131)
                    ·
                      rfl

theorem cell22_80521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 4, 3].length) (baseStart_80521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_80521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_80521 prefixEnd_80521 := by exact prefixLift 80521
  have htrace : WordTrace (prefixWord ++ tailWord_80521) baseStart_80521 baseEnd_80521 := by
    simpa [prefixWord, tailWord_80521, baseEnd_80521] using wordTrace_append hprefix tailTrace_80521
  have hstable : (prefixWord ++ tailWord_80521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80521).length < 2 ^ (prefixWord ++ tailWord_80521).sum := by decide
  have hdescent : baseEnd_80521 < baseStart_80521 := by decide
  rcases family_descends (prefixWord ++ tailWord_80521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80536 : List Nat := [2, 1, 2, 4, 1, 1, 2, 1, 4, 4]
def baseStart_80536 : Nat := 118140960795 + 80536 * 2 ^ 59
def prefixEnd_80536 : Nat := 4983230072969 + 3 ^ 40 * 80536 * 2
def baseEnd_80536 : Nat := 27569118660401424153085

theorem tailTrace_80536 : CollatzResearch.WordTrace tailWord_80536 prefixEnd_80536 27569118660401424153085 := by
  unfold tailWord_80536
  simp only [CollatzResearch.WordTrace]
  refine ⟨1468694618119650649430731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1958259490826200865907641 1468694618119650649430731)
  ·
    refine ⟨2203041927179475974146097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1468694618119650649430731 2203041927179475974146097)
    ·
      refine ⟨1652281445384606980609573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2203041927179475974146097 1652281445384606980609573)
      ·
        refine ⟨309802771009613808864295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1652281445384606980609573 309802771009613808864295)
        ·
          refine ⟨464704156514420713296443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309802771009613808864295 464704156514420713296443)
          ·
            refine ⟨697056234771631069944665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464704156514420713296443 697056234771631069944665)
            ·
              refine ⟨522792176078723302458499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 697056234771631069944665 522792176078723302458499)
              ·
                refine ⟨784188264118084953687749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 522792176078723302458499 784188264118084953687749)
                ·
                  refine ⟨147035299522140928816453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 784188264118084953687749 147035299522140928816453)
                  ·
                    refine ⟨27569118660401424153085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 147035299522140928816453 27569118660401424153085)
                    ·
                      rfl

theorem cell22_80536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 4, 4].length) (baseStart_80536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_80536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_80536 prefixEnd_80536 := by exact prefixLift 80536
  have htrace : WordTrace (prefixWord ++ tailWord_80536) baseStart_80536 baseEnd_80536 := by
    simpa [prefixWord, tailWord_80536, baseEnd_80536] using wordTrace_append hprefix tailTrace_80536
  have hstable : (prefixWord ++ tailWord_80536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80536).length < 2 ^ (prefixWord ++ tailWord_80536).sum := by decide
  have hdescent : baseEnd_80536 < baseStart_80536 := by decide
  rcases family_descends (prefixWord ++ tailWord_80536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80600 : List Nat := [2, 1, 2, 2, 3, 4, 1, 1, 3, 3]
def baseStart_80600 : Nat := 118140960795 + 80600 * 2 ^ 59
def prefixEnd_80600 : Nat := 4983230072969 + 3 ^ 40 * 80600 * 2
def baseEnd_80600 : Nat := 27591027168326590552889

theorem tailTrace_80600 : CollatzResearch.WordTrace tailWord_80600 prefixEnd_80600 27591027168326590552889 := by
  unfold tailWord_80600
  simp only [CollatzResearch.WordTrace]
  refine ⟨1469861754003720114595627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1959815672004960152794169 1469861754003720114595627)
  ·
    refine ⟨2204792631005580171893441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1469861754003720114595627 2204792631005580171893441)
    ·
      refine ⟨1653594473254185128920081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2204792631005580171893441 1653594473254185128920081)
      ·
        refine ⟨1240195854940638846690061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1653594473254185128920081 1240195854940638846690061)
        ·
          refine ⟨465073445602739567508773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1240195854940638846690061 465073445602739567508773)
          ·
            refine ⟨87201271050513668907895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 465073445602739567508773 87201271050513668907895)
            ·
              refine ⟨130801906575770503361843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87201271050513668907895 130801906575770503361843)
              ·
                refine ⟨196202859863655755042765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130801906575770503361843 196202859863655755042765)
                ·
                  refine ⟨73576072448870908141037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 196202859863655755042765 73576072448870908141037)
                  ·
                    refine ⟨27591027168326590552889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73576072448870908141037 27591027168326590552889)
                    ·
                      rfl

theorem cell22_80600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 3, 3].length) (baseStart_80600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_80600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_80600 prefixEnd_80600 := by exact prefixLift 80600
  have htrace : WordTrace (prefixWord ++ tailWord_80600) baseStart_80600 baseEnd_80600 := by
    simpa [prefixWord, tailWord_80600, baseEnd_80600] using wordTrace_append hprefix tailTrace_80600
  have hstable : (prefixWord ++ tailWord_80600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80600).length < 2 ^ (prefixWord ++ tailWord_80600).sum := by decide
  have hdescent : baseEnd_80600 < baseStart_80600 := by decide
  rcases family_descends (prefixWord ++ tailWord_80600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80613 : List Nat := [1, 3, 1, 4, 1, 3, 1, 3, 5]
def baseStart_80613 : Nat := 118140960795 + 80613 * 2 ^ 59
def prefixEnd_80613 : Nat := 4983230072969 + 3 ^ 40 * 80613 * 2
def baseEnd_80613 : Nat := 9198492444666296659283

theorem tailTrace_80613 : CollatzResearch.WordTrace tailWord_80613 prefixEnd_80613 9198492444666296659283 := by
  unfold tailWord_80613
  simp only [CollatzResearch.WordTrace]
  refine ⟨2940197656960343449414493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1960131771306895632942995 2940197656960343449414493)
  ·
    refine ⟨1102574121360128793530435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2940197656960343449414493 1102574121360128793530435)
    ·
      refine ⟨1653861182040193190295653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1102574121360128793530435 1653861182040193190295653)
      ·
        refine ⟨310098971632536223180435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1653861182040193190295653 310098971632536223180435)
        ·
          refine ⟨465148457448804334770653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310098971632536223180435 465148457448804334770653)
          ·
            refine ⟨174430671543301625538995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 465148457448804334770653 174430671543301625538995)
            ·
              refine ⟨261646007314952438308493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174430671543301625538995 261646007314952438308493)
              ·
                refine ⟨98117252743107164365685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 261646007314952438308493 98117252743107164365685)
                ·
                  refine ⟨9198492444666296659283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 98117252743107164365685 9198492444666296659283)
                  ·
                    rfl

theorem cell22_80613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 5].length) (baseStart_80613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_80613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_80613 prefixEnd_80613 := by exact prefixLift 80613
  have htrace : WordTrace (prefixWord ++ tailWord_80613) baseStart_80613 baseEnd_80613 := by
    simpa [prefixWord, tailWord_80613, baseEnd_80613] using wordTrace_append hprefix tailTrace_80613
  have hstable : (prefixWord ++ tailWord_80613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80613).length < 2 ^ (prefixWord ++ tailWord_80613).sum := by decide
  have hdescent : baseEnd_80613 < baseStart_80613 := by decide
  rcases family_descends (prefixWord ++ tailWord_80613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80673 : List Nat := [1, 2, 3, 2, 1, 2, 4, 1, 1, 5]
def baseStart_80673 : Nat := 118140960795 + 80673 * 2 ^ 59
def prefixEnd_80673 : Nat := 4983230072969 + 3 ^ 40 * 80673 * 2
def baseEnd_80673 : Nat := 27616016560178733477665

theorem tailTrace_80673 : CollatzResearch.WordTrace tailWord_80673 prefixEnd_80673 27616016560178733477665 := by
  unfold tailWord_80673
  simp only [CollatzResearch.WordTrace]
  refine ⟨2942386036742973696598673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1961590691161982464399115 2942386036742973696598673)
  ·
    refine ⟨2206789527557230272449005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2942386036742973696598673 2206789527557230272449005)
    ·
      refine ⟨827546072833961352168377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2206789527557230272449005 827546072833961352168377)
      ·
        refine ⟨620659554625471014126283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 827546072833961352168377 620659554625471014126283)
        ·
          refine ⟨930989331938206521189425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 620659554625471014126283 930989331938206521189425)
          ·
            refine ⟨698241998953654890892069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 930989331938206521189425 698241998953654890892069)
            ·
              refine ⟨130920374803810292042263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 698241998953654890892069 130920374803810292042263)
              ·
                refine ⟨196380562205715438063395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130920374803810292042263 196380562205715438063395)
                ·
                  refine ⟨294570843308573157095093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 196380562205715438063395 294570843308573157095093)
                  ·
                    refine ⟨27616016560178733477665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 294570843308573157095093 27616016560178733477665)
                    ·
                      rfl

theorem cell22_80673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_80673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_80673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_80673 prefixEnd_80673 := by exact prefixLift 80673
  have htrace : WordTrace (prefixWord ++ tailWord_80673) baseStart_80673 baseEnd_80673 := by
    simpa [prefixWord, tailWord_80673, baseEnd_80673] using wordTrace_append hprefix tailTrace_80673
  have hstable : (prefixWord ++ tailWord_80673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80673).length < 2 ^ (prefixWord ++ tailWord_80673).sum := by decide
  have hdescent : baseEnd_80673 < baseStart_80673 := by decide
  rcases family_descends (prefixWord ++ tailWord_80673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80724 : List Nat := [2, 4, 1, 1, 4, 1, 3, 1, 2, 3]
def baseStart_80724 : Nat := 118140960795 + 80724 * 2 ^ 59
def prefixEnd_80724 : Nat := 4983230072969 + 3 ^ 40 * 80724 * 2
def baseEnd_80724 : Nat := 27633474902431600452509

theorem tailTrace_80724 : CollatzResearch.WordTrace tailWord_80724 prefixEnd_80724 27633474902431600452509 := by
  unfold tailWord_80724
  simp only [CollatzResearch.WordTrace]
  refine ⟨1472123079779104703352613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1962830773038806271136817 1472123079779104703352613)
  ·
    refine ⟨276023077458582131878615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1472123079779104703352613 276023077458582131878615)
    ·
      refine ⟨414034616187873197817923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 276023077458582131878615 414034616187873197817923)
      ·
        refine ⟨621051924281809796726885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 414034616187873197817923 621051924281809796726885)
        ·
          refine ⟨116447235802839336886291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 621051924281809796726885 116447235802839336886291)
          ·
            refine ⟨174670853704259005329437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116447235802839336886291 174670853704259005329437)
            ·
              refine ⟨65501570139097126998539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 174670853704259005329437 65501570139097126998539)
              ·
                refine ⟨98252355208645690497809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65501570139097126998539 98252355208645690497809)
                ·
                  refine ⟨73689266406484267873357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98252355208645690497809 73689266406484267873357)
                  ·
                    refine ⟨27633474902431600452509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73689266406484267873357 27633474902431600452509)
                    ·
                      rfl

theorem cell22_80724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_80724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_80724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_80724 prefixEnd_80724 := by exact prefixLift 80724
  have htrace : WordTrace (prefixWord ++ tailWord_80724) baseStart_80724 baseEnd_80724 := by
    simpa [prefixWord, tailWord_80724, baseEnd_80724] using wordTrace_append hprefix tailTrace_80724
  have hstable : (prefixWord ++ tailWord_80724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80724).length < 2 ^ (prefixWord ++ tailWord_80724).sum := by decide
  have hdescent : baseEnd_80724 < baseStart_80724 := by decide
  rcases family_descends (prefixWord ++ tailWord_80724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80752 : List Nat := [2, 1, 1, 1, 4, 1, 5, 3, 1, 3]
def baseStart_80752 : Nat := 118140960795 + 80752 * 2 ^ 59
def prefixEnd_80752 : Nat := 4983230072969 + 3 ^ 40 * 80752 * 2
def baseEnd_80752 : Nat := 27643059874648860752423

theorem tailTrace_80752 : CollatzResearch.WordTrace tailWord_80752 prefixEnd_80752 27643059874648860752423 := by
  unfold tailWord_80752
  simp only [CollatzResearch.WordTrace]
  refine ⟨1472633701728385094362255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1963511602304513459149673 1472633701728385094362255)
  ·
    refine ⟨2208950552592577641543383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1472633701728385094362255 2208950552592577641543383)
    ·
      refine ⟨3313425828888866462315075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2208950552592577641543383 3313425828888866462315075)
      ·
        refine ⟨4970138743333299693472613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3313425828888866462315075 4970138743333299693472613)
        ·
          refine ⟨931901014374993692526115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4970138743333299693472613 931901014374993692526115)
          ·
            refine ⟨1397851521562490538789173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 931901014374993692526115 1397851521562490538789173)
            ·
              refine ⟨131048580146483488011485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1397851521562490538789173 131048580146483488011485)
              ·
                refine ⟨49143217554931308004307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131048580146483488011485 49143217554931308004307)
                ·
                  refine ⟨73714826332396962006461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49143217554931308004307 73714826332396962006461)
                  ·
                    refine ⟨27643059874648860752423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73714826332396962006461 27643059874648860752423)
                    ·
                      rfl

theorem cell22_80752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 3, 1, 3].length) (baseStart_80752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_80752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_80752 prefixEnd_80752 := by exact prefixLift 80752
  have htrace : WordTrace (prefixWord ++ tailWord_80752) baseStart_80752 baseEnd_80752 := by
    simpa [prefixWord, tailWord_80752, baseEnd_80752] using wordTrace_append hprefix tailTrace_80752
  have hstable : (prefixWord ++ tailWord_80752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80752).length < 2 ^ (prefixWord ++ tailWord_80752).sum := by decide
  have hdescent : baseEnd_80752 < baseStart_80752 := by decide
  rcases family_descends (prefixWord ++ tailWord_80752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80857 : List Nat := [1, 2, 1, 2, 5, 3, 1, 1, 2, 4]
def baseStart_80857 : Nat := 118140960795 + 80857 * 2 ^ 59
def prefixEnd_80857 : Nat := 4983230072969 + 3 ^ 40 * 80857 * 2
def baseEnd_80857 : Nat := 27679003520463586877101

theorem tailTrace_80857 : CollatzResearch.WordTrace tailWord_80857 prefixEnd_80857 27679003520463586877101 := by
  unfold tailWord_80857
  simp only [CollatzResearch.WordTrace]
  refine ⟨2949097068076373121296825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1966064712050915414197883 2949097068076373121296825)
  ·
    refine ⟨2211822801057279840972619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2949097068076373121296825 2211822801057279840972619)
    ·
      refine ⟨3317734201585919761458929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2211822801057279840972619 3317734201585919761458929)
      ·
        refine ⟨2488300651189439821094197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3317734201585919761458929 2488300651189439821094197)
        ·
          refine ⟨233278186049009983227581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2488300651189439821094197 233278186049009983227581)
          ·
            refine ⟨87479319768378743710343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 233278186049009983227581 87479319768378743710343)
            ·
              refine ⟨131218979652568115565515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87479319768378743710343 131218979652568115565515)
              ·
                refine ⟨196828469478852173348273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131218979652568115565515 196828469478852173348273)
                ·
                  refine ⟨147621352109139130011205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 196828469478852173348273 147621352109139130011205)
                  ·
                    refine ⟨27679003520463586877101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 147621352109139130011205 27679003520463586877101)
                    ·
                      rfl

theorem cell22_80857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 1, 2, 4].length) (baseStart_80857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_80857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_80857 prefixEnd_80857 := by exact prefixLift 80857
  have htrace : WordTrace (prefixWord ++ tailWord_80857) baseStart_80857 baseEnd_80857 := by
    simpa [prefixWord, tailWord_80857, baseEnd_80857] using wordTrace_append hprefix tailTrace_80857
  have hstable : (prefixWord ++ tailWord_80857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80857).length < 2 ^ (prefixWord ++ tailWord_80857).sum := by decide
  have hdescent : baseEnd_80857 < baseStart_80857 := by decide
  rcases family_descends (prefixWord ++ tailWord_80857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80868 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 1, 8]
def baseStart_80868 : Nat := 118140960795 + 80868 * 2 ^ 59
def prefixEnd_80868 : Nat := 4983230072969 + 3 ^ 40 * 80868 * 2
def baseEnd_80868 : Nat := 27682769045263224852067

theorem tailTrace_80868 : CollatzResearch.WordTrace tailWord_80868 prefixEnd_80868 27682769045263224852067 := by
  unfold tailWord_80868
  simp only [CollatzResearch.WordTrace]
  refine ⟨1474749135518260999973629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1966332180691014666631505 1474749135518260999973629)
  ·
    refine ⟨553030925819347874990111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1474749135518260999973629 553030925819347874990111)
    ·
      refine ⟨829546388729021812485167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 553030925819347874990111 829546388729021812485167)
      ·
        refine ⟨1244319583093532718727751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 829546388729021812485167 1244319583093532718727751)
        ·
          refine ⟨1866479374640299078091627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1244319583093532718727751 1866479374640299078091627)
          ·
            refine ⟨2799719061960448617137441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1866479374640299078091627 2799719061960448617137441)
            ·
              refine ⟨2099789296470336462853081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2799719061960448617137441 2099789296470336462853081)
              ·
                refine ⟨1574841972352752347139811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2099789296470336462853081 1574841972352752347139811)
                ·
                  refine ⟨2362262958529128520709717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1574841972352752347139811 2362262958529128520709717)
                  ·
                    refine ⟨27682769045263224852067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2362262958529128520709717 27682769045263224852067)
                    ·
                      rfl

theorem cell22_80868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_80868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_80868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_80868 prefixEnd_80868 := by exact prefixLift 80868
  have htrace : WordTrace (prefixWord ++ tailWord_80868) baseStart_80868 baseEnd_80868 := by
    simpa [prefixWord, tailWord_80868, baseEnd_80868] using wordTrace_append hprefix tailTrace_80868
  have hstable : (prefixWord ++ tailWord_80868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80868).length < 2 ^ (prefixWord ++ tailWord_80868).sum := by decide
  have hdescent : baseEnd_80868 < baseStart_80868 := by decide
  rcases family_descends (prefixWord ++ tailWord_80868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80913 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 2, 8]
def baseStart_80913 : Nat := 118140960795 + 80913 * 2 ^ 59
def prefixEnd_80913 : Nat := 4983230072969 + 3 ^ 40 * 80913 * 2
def baseEnd_80913 : Nat := 27698173464898107476929

theorem tailTrace_80913 : CollatzResearch.WordTrace tailWord_80913 prefixEnd_80913 27698173464898107476929 := by
  unfold tailWord_80913
  simp only [CollatzResearch.WordTrace]
  refine ⟨2951139555873494685335393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1967426370582329790223595 2951139555873494685335393)
  ·
    refine ⟨2213354666905121014001545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2951139555873494685335393 2213354666905121014001545)
    ·
      refine ⟨1660016000178840760501159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2213354666905121014001545 1660016000178840760501159)
      ·
        refine ⟨2490024000268261140751739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1660016000178840760501159 2490024000268261140751739)
        ·
          refine ⟨3735036000402391711127609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2490024000268261140751739 3735036000402391711127609)
          ·
            refine ⟨2801277000301793783345707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3735036000402391711127609 2801277000301793783345707)
            ·
              refine ⟨4201915500452690675018561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2801277000301793783345707 4201915500452690675018561)
              ·
                refine ⟨3151436625339518006263921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4201915500452690675018561 3151436625339518006263921)
                ·
                  refine ⟨2363577469004638504697941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3151436625339518006263921 2363577469004638504697941)
                  ·
                    refine ⟨27698173464898107476929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2363577469004638504697941 27698173464898107476929)
                    ·
                      rfl

theorem cell22_80913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_80913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_80913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_80913 prefixEnd_80913 := by exact prefixLift 80913
  have htrace : WordTrace (prefixWord ++ tailWord_80913) baseStart_80913 baseEnd_80913 := by
    simpa [prefixWord, tailWord_80913, baseEnd_80913] using wordTrace_append hprefix tailTrace_80913
  have hstable : (prefixWord ++ tailWord_80913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80913).length < 2 ^ (prefixWord ++ tailWord_80913).sum := by decide
  have hdescent : baseEnd_80913 < baseStart_80913 := by decide
  rcases family_descends (prefixWord ++ tailWord_80913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80938 : List Nat := [3, 1, 4, 1, 3, 1, 3, 2, 1, 3]
def baseStart_80938 : Nat := 118140960795 + 80938 * 2 ^ 59
def prefixEnd_80938 : Nat := 4983230072969 + 3 ^ 40 * 80938 * 2
def baseEnd_80938 : Nat := 27706731475806375601853

theorem tailTrace_80938 : CollatzResearch.WordTrace tailWord_80938 prefixEnd_80938 27706731475806375601853 := by
  unfold tailWord_80938
  simp only [CollatzResearch.WordTrace]
  refine ⟨738012845195730988748867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1968034253855282636663645 738012845195730988748867)
  ·
    refine ⟨1107019267793596483123301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 738012845195730988748867 1107019267793596483123301)
    ·
      refine ⟨207566112711299340585619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1107019267793596483123301 207566112711299340585619)
      ·
        refine ⟨311349169066949010878429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207566112711299340585619 311349169066949010878429)
        ·
          refine ⟨116755938400105879079411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 311349169066949010878429 116755938400105879079411)
          ·
            refine ⟨175133907600158818619117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116755938400105879079411 175133907600158818619117)
            ·
              refine ⟨65675215350059556982169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175133907600158818619117 65675215350059556982169)
              ·
                refine ⟨49256411512544667736627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65675215350059556982169 49256411512544667736627)
                ·
                  refine ⟨73884617268817001604941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49256411512544667736627 73884617268817001604941)
                  ·
                    refine ⟨27706731475806375601853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73884617268817001604941 27706731475806375601853)
                    ·
                      rfl

theorem cell22_80938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_80938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_80938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_80938 prefixEnd_80938 := by exact prefixLift 80938
  have htrace : WordTrace (prefixWord ++ tailWord_80938) baseStart_80938 baseEnd_80938 := by
    simpa [prefixWord, tailWord_80938, baseEnd_80938] using wordTrace_append hprefix tailTrace_80938
  have hstable : (prefixWord ++ tailWord_80938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80938).length < 2 ^ (prefixWord ++ tailWord_80938).sum := by decide
  have hdescent : baseEnd_80938 < baseStart_80938 := by decide
  rcases family_descends (prefixWord ++ tailWord_80938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80960 : List Nat := [2, 1, 1, 2, 2, 3, 2, 3, 1, 5]
def baseStart_80960 : Nat := 118140960795 + 80960 * 2 ^ 59
def prefixEnd_80960 : Nat := 4983230072969 + 3 ^ 40 * 80960 * 2
def baseEnd_80960 : Nat := 27714262525405651551785

theorem tailTrace_80960 : CollatzResearch.WordTrace tailWord_80960 prefixEnd_80960 27714262525405651551785 := by
  unfold tailWord_80960
  simp only [CollatzResearch.WordTrace]
  refine ⟨1476426893351610856148167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1968569191135481141530889 1476426893351610856148167)
  ·
    refine ⟨2214640340027416284222251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1476426893351610856148167 2214640340027416284222251)
    ·
      refine ⟨3321960510041124426333377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2214640340027416284222251 3321960510041124426333377)
      ·
        refine ⟨2491470382530843319750033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3321960510041124426333377 2491470382530843319750033)
        ·
          refine ⟨1868602786898132489812525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2491470382530843319750033 1868602786898132489812525)
          ·
            refine ⟨700726045086799683679697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1868602786898132489812525 700726045086799683679697)
            ·
              refine ⟨525544533815099762759773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 700726045086799683679697 525544533815099762759773)
              ·
                refine ⟨197079200180662411034915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 525544533815099762759773 197079200180662411034915)
                ·
                  refine ⟨295618800270993616552373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 197079200180662411034915 295618800270993616552373)
                  ·
                    refine ⟨27714262525405651551785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 295618800270993616552373 27714262525405651551785)
                    ·
                      rfl

theorem cell22_80960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 1, 5].length) (baseStart_80960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_80960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_80960 prefixEnd_80960 := by exact prefixLift 80960
  have htrace : WordTrace (prefixWord ++ tailWord_80960) baseStart_80960 baseEnd_80960 := by
    simpa [prefixWord, tailWord_80960, baseEnd_80960] using wordTrace_append hprefix tailTrace_80960
  have hstable : (prefixWord ++ tailWord_80960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80960).length < 2 ^ (prefixWord ++ tailWord_80960).sum := by decide
  have hdescent : baseEnd_80960 < baseStart_80960 := by decide
  rcases family_descends (prefixWord ++ tailWord_80960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81020 : List Nat := [2, 2, 2, 1, 1, 3, 1, 2, 2, 6]
def baseStart_81020 : Nat := 118140960795 + 81020 * 2 ^ 59
def prefixEnd_81020 : Nat := 4983230072969 + 3 ^ 40 * 81020 * 2
def baseEnd_81020 : Nat := 27734801751585495051601

theorem tailTrace_81020 : CollatzResearch.WordTrace tailWord_81020 prefixEnd_81020 27734801751585495051601 := by
  unfold tailWord_81020
  simp only [CollatzResearch.WordTrace]
  refine ⟨1477521083242925979740257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1970028110990567972987009 1477521083242925979740257)
  ·
    refine ⟨1108140812432194484805193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1477521083242925979740257 1108140812432194484805193)
    ·
      refine ⟨831105609324145863603895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1108140812432194484805193 831105609324145863603895)
      ·
        refine ⟨1246658413986218795405843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 831105609324145863603895 1246658413986218795405843)
        ·
          refine ⟨1869987620979328193108765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1246658413986218795405843 1869987620979328193108765)
          ·
            refine ⟨701245357867248072415787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1869987620979328193108765 701245357867248072415787)
            ·
              refine ⟨1051868036800872108623681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 701245357867248072415787 1051868036800872108623681)
              ·
                refine ⟨788901027600654081467761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1051868036800872108623681 788901027600654081467761)
                ·
                  refine ⟨591675770700490561100821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 788901027600654081467761 591675770700490561100821)
                  ·
                    refine ⟨27734801751585495051601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 591675770700490561100821 27734801751585495051601)
                    ·
                      rfl

theorem cell22_81020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_81020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_81020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_81020 prefixEnd_81020 := by exact prefixLift 81020
  have htrace : WordTrace (prefixWord ++ tailWord_81020) baseStart_81020 baseEnd_81020 := by
    simpa [prefixWord, tailWord_81020, baseEnd_81020] using wordTrace_append hprefix tailTrace_81020
  have hstable : (prefixWord ++ tailWord_81020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81020).length < 2 ^ (prefixWord ++ tailWord_81020).sum := by decide
  have hdescent : baseEnd_81020 < baseStart_81020 := by decide
  rcases family_descends (prefixWord ++ tailWord_81020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81052 : List Nat := [2, 2, 3, 2, 1, 3, 1, 1, 7]
def baseStart_81052 : Nat := 118140960795 + 81052 * 2 ^ 59
def prefixEnd_81052 : Nat := 4983230072969 + 3 ^ 40 * 81052 * 2
def baseEnd_81052 : Nat := 9248585335182692750501

theorem tailTrace_81052 : CollatzResearch.WordTrace tailWord_81052 prefixEnd_81052 9248585335182692750501 := by
  unfold tailWord_81052
  simp only [CollatzResearch.WordTrace]
  refine ⟨1478104651184960712322705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1970806201579947616430273 1478104651184960712322705)
  ·
    refine ⟨1108578488388720534242029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1478104651184960712322705 1108578488388720534242029)
    ·
      refine ⟨415716933145770200340761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1108578488388720534242029 415716933145770200340761)
      ·
        refine ⟨311787699859327650255571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 415716933145770200340761 311787699859327650255571)
        ·
          refine ⟨467681549788991475383357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311787699859327650255571 467681549788991475383357)
          ·
            refine ⟨175380581170871803268759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 467681549788991475383357 175380581170871803268759)
            ·
              refine ⟨263070871756307704903139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175380581170871803268759 263070871756307704903139)
              ·
                refine ⟨394606307634461557354709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 263070871756307704903139 394606307634461557354709)
                ·
                  refine ⟨9248585335182692750501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 394606307634461557354709 9248585335182692750501)
                  ·
                    rfl

theorem cell22_81052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 7].length) (baseStart_81052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_81052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_81052 prefixEnd_81052 := by exact prefixLift 81052
  have htrace : WordTrace (prefixWord ++ tailWord_81052) baseStart_81052 baseEnd_81052 := by
    simpa [prefixWord, tailWord_81052, baseEnd_81052] using wordTrace_append hprefix tailTrace_81052
  have hstable : (prefixWord ++ tailWord_81052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81052).length < 2 ^ (prefixWord ++ tailWord_81052).sum := by decide
  have hdescent : baseEnd_81052 < baseStart_81052 := by decide
  rcases family_descends (prefixWord ++ tailWord_81052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81080 : List Nat := [2, 1, 2, 1, 2, 1, 2, 3, 8]
def baseStart_81080 : Nat := 118140960795 + 81080 * 2 ^ 59
def prefixEnd_81080 : Nat := 4983230072969 + 3 ^ 40 * 81080 * 2
def baseEnd_81080 : Nat := 9251780325921779517139

theorem tailTrace_81080 : CollatzResearch.WordTrace tailWord_81080 prefixEnd_81080 9251780325921779517139 := by
  unfold tailWord_81080
  simp only [CollatzResearch.WordTrace]
  refine ⟨1478615273134241103332347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1971487030845654804443129 1478615273134241103332347)
  ·
    refine ⟨2217922909701361654998521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1478615273134241103332347 2217922909701361654998521)
    ·
      refine ⟨1663442182276021241248891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2217922909701361654998521 1663442182276021241248891)
      ·
        refine ⟨2495163273414031861873337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1663442182276021241248891 2495163273414031861873337)
        ·
          refine ⟨1871372455060523896405003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2495163273414031861873337 1871372455060523896405003)
          ·
            refine ⟨2807058682590785844607505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1871372455060523896405003 2807058682590785844607505)
            ·
              refine ⟨2105294011943089383455629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2807058682590785844607505 2105294011943089383455629)
              ·
                refine ⟨789485254478658518795861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2105294011943089383455629 789485254478658518795861)
                ·
                  refine ⟨9251780325921779517139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 789485254478658518795861 9251780325921779517139)
                  ·
                    rfl

theorem cell22_81080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 8].length) (baseStart_81080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_81080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_81080 prefixEnd_81080 := by exact prefixLift 81080
  have htrace : WordTrace (prefixWord ++ tailWord_81080) baseStart_81080 baseEnd_81080 := by
    simpa [prefixWord, tailWord_81080, baseEnd_81080] using wordTrace_append hprefix tailTrace_81080
  have hstable : (prefixWord ++ tailWord_81080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81080).length < 2 ^ (prefixWord ++ tailWord_81080).sum := by decide
  have hdescent : baseEnd_81080 < baseStart_81080 := by decide
  rcases family_descends (prefixWord ++ tailWord_81080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81204 : List Nat := [2, 5, 1, 1, 1, 1, 2, 2, 7]
def baseStart_81204 : Nat := 118140960795 + 81204 * 2 ^ 59
def prefixEnd_81204 : Nat := 4983230072969 + 3 ^ 40 * 81204 * 2
def baseEnd_81204 : Nat := 9265929570623449483679

theorem tailTrace_81204 : CollatzResearch.WordTrace tailWord_81204 prefixEnd_81204 9265929570623449483679 := by
  unfold tailWord_81204
  simp only [CollatzResearch.WordTrace]
  refine ⟨1480876598909625692089333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1974502131879500922785777 1480876598909625692089333)
  ·
    refine ⟨138832181147777408633375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1480876598909625692089333 138832181147777408633375)
    ·
      refine ⟨208248271721666112950063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138832181147777408633375 208248271721666112950063)
      ·
        refine ⟨312372407582499169425095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208248271721666112950063 312372407582499169425095)
        ·
          refine ⟨468558611373748754137643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312372407582499169425095 468558611373748754137643)
          ·
            refine ⟨702837917060623131206465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468558611373748754137643 702837917060623131206465)
            ·
              refine ⟨527128437795467348404849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 702837917060623131206465 527128437795467348404849)
              ·
                refine ⟨395346328346600511303637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 527128437795467348404849 395346328346600511303637)
                ·
                  refine ⟨9265929570623449483679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 395346328346600511303637 9265929570623449483679)
                  ·
                    rfl

theorem cell22_81204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_81204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_81204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_81204 prefixEnd_81204 := by exact prefixLift 81204
  have htrace : WordTrace (prefixWord ++ tailWord_81204) baseStart_81204 baseEnd_81204 := by
    simpa [prefixWord, tailWord_81204, baseEnd_81204] using wordTrace_append hprefix tailTrace_81204
  have hstable : (prefixWord ++ tailWord_81204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81204).length < 2 ^ (prefixWord ++ tailWord_81204).sum := by decide
  have hdescent : baseEnd_81204 < baseStart_81204 := by decide
  rcases family_descends (prefixWord ++ tailWord_81204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81251 : List Nat := [1, 1, 1, 5, 2, 3, 2, 2, 1, 4]
def baseStart_81251 : Nat := 118140960795 + 81251 * 2 ^ 59
def prefixEnd_81251 : Nat := 4983230072969 + 3 ^ 40 * 81251 * 2
def baseEnd_81251 : Nat := 27813877772377892525893

theorem tailTrace_81251 : CollatzResearch.WordTrace tailWord_81251 prefixEnd_81251 27813877772377892525893 := by
  unfold tailWord_81251
  simp only [CollatzResearch.WordTrace]
  refine ⟨2963467428648978411139607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1975644952432652274093071 2963467428648978411139607)
  ·
    refine ⟨4445201142973467616709411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2963467428648978411139607 4445201142973467616709411)
    ·
      refine ⟨6667801714460201425064117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4445201142973467616709411 6667801714460201425064117)
      ·
        refine ⟨625106410730643883599761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6667801714460201425064117 625106410730643883599761)
        ·
          refine ⟨468829808047982912699821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 625106410730643883599761 468829808047982912699821)
          ·
            refine ⟨175811178017993592262433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 468829808047982912699821 175811178017993592262433)
            ·
              refine ⟨131858383513495194196825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175811178017993592262433 131858383513495194196825)
              ·
                refine ⟨98893787635121395647619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131858383513495194196825 98893787635121395647619)
                ·
                  refine ⟨148340681452682093471429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 98893787635121395647619 148340681452682093471429)
                  ·
                    refine ⟨27813877772377892525893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 148340681452682093471429 27813877772377892525893)
                    ·
                      rfl

theorem cell22_81251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 2, 1, 4].length) (baseStart_81251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_81251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_81251 prefixEnd_81251 := by exact prefixLift 81251
  have htrace : WordTrace (prefixWord ++ tailWord_81251) baseStart_81251 baseEnd_81251 := by
    simpa [prefixWord, tailWord_81251, baseEnd_81251] using wordTrace_append hprefix tailTrace_81251
  have hstable : (prefixWord ++ tailWord_81251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81251).length < 2 ^ (prefixWord ++ tailWord_81251).sum := by decide
  have hdescent : baseEnd_81251 < baseStart_81251 := by decide
  rcases family_descends (prefixWord ++ tailWord_81251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81264 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 6, 3]
def baseStart_81264 : Nat := 118140960795 + 81264 * 2 ^ 59
def prefixEnd_81264 : Nat := 4983230072969 + 3 ^ 40 * 81264 * 2
def baseEnd_81264 : Nat := 27818327938050191950853

theorem tailTrace_81264 : CollatzResearch.WordTrace tailWord_81264 prefixEnd_81264 27818327938050191950853 := by
  unfold tailWord_81264
  simp only [CollatzResearch.WordTrace]
  refine ⟨1481970788800940815681423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1975961051734587754241897 1481970788800940815681423)
  ·
    refine ⟨2222956183201411223522135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1481970788800940815681423 2222956183201411223522135)
    ·
      refine ⟨3334434274802116835283203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2222956183201411223522135 3334434274802116835283203)
      ·
        refine ⟨5001651412203175252924805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3334434274802116835283203 5001651412203175252924805)
        ·
          refine ⟨937809639788095359923401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5001651412203175252924805 937809639788095359923401)
          ·
            refine ⟨703357229841071519942551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 937809639788095359923401 703357229841071519942551)
            ·
              refine ⟨1055035844761607279913827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 703357229841071519942551 1055035844761607279913827)
              ·
                refine ⟨1582553767142410919870741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1055035844761607279913827 1582553767142410919870741)
                ·
                  refine ⟨74182207834800511868941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1582553767142410919870741 74182207834800511868941)
                  ·
                    refine ⟨27818327938050191950853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74182207834800511868941 27818327938050191950853)
                    ·
                      rfl

theorem cell22_81264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 6, 3].length) (baseStart_81264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_81264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_81264 prefixEnd_81264 := by exact prefixLift 81264
  have htrace : WordTrace (prefixWord ++ tailWord_81264) baseStart_81264 baseEnd_81264 := by
    simpa [prefixWord, tailWord_81264, baseEnd_81264] using wordTrace_append hprefix tailTrace_81264
  have hstable : (prefixWord ++ tailWord_81264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81264).length < 2 ^ (prefixWord ++ tailWord_81264).sum := by decide
  have hdescent : baseEnd_81264 < baseStart_81264 := by decide
  rcases family_descends (prefixWord ++ tailWord_81264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81283 : List Nat := [1, 1, 1, 3, 5, 2, 3, 2, 4]
def baseStart_81283 : Nat := 118140960795 + 81283 * 2 ^ 59
def prefixEnd_81283 : Nat := 4983230072969 + 3 ^ 40 * 81283 * 2
def baseEnd_81283 : Nat := 9274944008780158575265

theorem tailTrace_81283 : CollatzResearch.WordTrace tailWord_81283 prefixEnd_81283 9274944008780158575265 := by
  unfold tailWord_81283
  simp only [CollatzResearch.WordTrace]
  refine ⟨2964634564533047876304503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1976423043022031917536335 2964634564533047876304503)
  ·
    refine ⟨4446951846799571814456755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2964634564533047876304503 4446951846799571814456755)
    ·
      refine ⟨6670427770199357721685133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4446951846799571814456755 6670427770199357721685133)
      ·
        refine ⟨2501410413824759145631925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6670427770199357721685133 2501410413824759145631925)
        ·
          refine ⟨234507226296071169902993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2501410413824759145631925 234507226296071169902993)
          ·
            refine ⟨175880419722053377427245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 234507226296071169902993 175880419722053377427245)
            ·
              refine ⟨65955157395770016535217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175880419722053377427245 65955157395770016535217)
              ·
                refine ⟨49466368046827512401413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65955157395770016535217 49466368046827512401413)
                ·
                  refine ⟨9274944008780158575265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49466368046827512401413 9274944008780158575265)
                  ·
                    rfl

theorem cell22_81283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 2, 4].length) (baseStart_81283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_81283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_81283 prefixEnd_81283 := by exact prefixLift 81283
  have htrace : WordTrace (prefixWord ++ tailWord_81283) baseStart_81283 baseEnd_81283 := by
    simpa [prefixWord, tailWord_81283, baseEnd_81283] using wordTrace_append hprefix tailTrace_81283
  have hstable : (prefixWord ++ tailWord_81283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81283).length < 2 ^ (prefixWord ++ tailWord_81283).sum := by decide
  have hdescent : baseEnd_81283 < baseStart_81283 := by decide
  rcases family_descends (prefixWord ++ tailWord_81283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81307 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 5, 8]
def baseStart_81307 : Nat := 118140960795 + 81307 * 2 ^ 59
def prefixEnd_81307 : Nat := 4983230072969 + 3 ^ 40 * 81307 * 2
def baseEnd_81307 : Nat := 27833047716812413125721

theorem tailTrace_81307 : CollatzResearch.WordTrace tailWord_81307 prefixEnd_81307 27833047716812413125721 := by
  unfold tailWord_81307
  simp only [CollatzResearch.WordTrace]
  refine ⟨2965509916446099975178175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1977006610964066650118783 2965509916446099975178175)
  ·
    refine ⟨4448264874669149962767263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2965509916446099975178175 4448264874669149962767263)
    ·
      refine ⟨6672397312003724944150895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4448264874669149962767263 6672397312003724944150895)
      ·
        refine ⟨10008595968005587416226343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6672397312003724944150895 10008595968005587416226343)
        ·
          refine ⟨15012893952008381124339515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10008595968005587416226343 15012893952008381124339515)
          ·
            refine ⟨22519340928012571686509273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15012893952008381124339515 22519340928012571686509273)
            ·
              refine ⟨16889505696009428764881955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22519340928012571686509273 16889505696009428764881955)
              ·
                refine ⟨25334258544014143147322933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16889505696009428764881955 25334258544014143147322933)
                ·
                  refine ⟨2375086738501325920061525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25334258544014143147322933 2375086738501325920061525)
                  ·
                    refine ⟨27833047716812413125721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2375086738501325920061525 27833047716812413125721)
                    ·
                      rfl

theorem cell22_81307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 8].length) (baseStart_81307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_81307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_81307 prefixEnd_81307 := by exact prefixLift 81307
  have htrace : WordTrace (prefixWord ++ tailWord_81307) baseStart_81307 baseEnd_81307 := by
    simpa [prefixWord, tailWord_81307, baseEnd_81307] using wordTrace_append hprefix tailTrace_81307
  have hstable : (prefixWord ++ tailWord_81307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81307).length < 2 ^ (prefixWord ++ tailWord_81307).sum := by decide
  have hdescent : baseEnd_81307 < baseStart_81307 := by decide
  rcases family_descends (prefixWord ++ tailWord_81307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81354 : List Nat := [3, 1, 2, 1, 2, 3, 1, 1, 1, 7]
def baseStart_81354 : Nat := 118140960795 + 81354 * 2 ^ 59
def prefixEnd_81354 : Nat := 4983230072969 + 3 ^ 40 * 81354 * 2
def baseEnd_81354 : Nat := 27849136777319957200577

theorem tailTrace_81354 : CollatzResearch.WordTrace tailWord_81354 prefixEnd_81354 27849136777319957200577 := by
  unfold tailWord_81354
  simp only [CollatzResearch.WordTrace]
  refine ⟨741806036818956750534779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1978149431517218001426077 741806036818956750534779)
  ·
    refine ⟨1112709055228435125802169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 741806036818956750534779 1112709055228435125802169)
    ·
      refine ⟨834531791421326344351627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1112709055228435125802169 834531791421326344351627)
      ·
        refine ⟨1251797687131989516527441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 834531791421326344351627 1251797687131989516527441)
        ·
          refine ⟨938848265348992137395581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1251797687131989516527441 938848265348992137395581)
          ·
            refine ⟨352068099505872051523343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 938848265348992137395581 352068099505872051523343)
            ·
              refine ⟨528102149258808077285015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 352068099505872051523343 528102149258808077285015)
              ·
                refine ⟨792153223888212115927523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 528102149258808077285015 792153223888212115927523)
                ·
                  refine ⟨1188229835832318173891285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 792153223888212115927523 1188229835832318173891285)
                  ·
                    refine ⟨27849136777319957200577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1188229835832318173891285 27849136777319957200577)
                    ·
                      rfl

theorem cell22_81354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_81354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_81354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_81354 prefixEnd_81354 := by exact prefixLift 81354
  have htrace : WordTrace (prefixWord ++ tailWord_81354) baseStart_81354 baseEnd_81354 := by
    simpa [prefixWord, tailWord_81354, baseEnd_81354] using wordTrace_append hprefix tailTrace_81354
  have hstable : (prefixWord ++ tailWord_81354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81354).length < 2 ^ (prefixWord ++ tailWord_81354).sum := by decide
  have hdescent : baseEnd_81354 < baseStart_81354 := by decide
  rcases family_descends (prefixWord ++ tailWord_81354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81356 : List Nat := [2, 2, 1, 4, 2, 1, 2, 3, 5]
def baseStart_81356 : Nat := 118140960795 + 81356 * 2 ^ 59
def prefixEnd_81356 : Nat := 4983230072969 + 3 ^ 40 * 81356 * 2
def baseEnd_81356 : Nat := 9283273806064206216857

theorem tailTrace_81356 : CollatzResearch.WordTrace tailWord_81356 prefixEnd_81356 9283273806064206216857 := by
  unfold tailWord_81356
  simp only [CollatzResearch.WordTrace]
  refine ⟨1483648546634290671855961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1978198062179054229141281 1483648546634290671855961)
  ·
    refine ⟨1112736409975718003891971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1483648546634290671855961 1112736409975718003891971)
    ·
      refine ⟨1669104614963577005837957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1112736409975718003891971 1669104614963577005837957)
      ·
        refine ⟨312957115305670688594617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1669104614963577005837957 312957115305670688594617)
        ·
          refine ⟨234717836479253016445963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 312957115305670688594617 234717836479253016445963)
          ·
            refine ⟨352076754718879524668945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234717836479253016445963 352076754718879524668945)
            ·
              refine ⟨264057566039159643501709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 352076754718879524668945 264057566039159643501709)
              ·
                refine ⟨99021587264684866313141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 264057566039159643501709 99021587264684866313141)
                ·
                  refine ⟨9283273806064206216857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 99021587264684866313141 9283273806064206216857)
                  ·
                    rfl

theorem cell22_81356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 5].length) (baseStart_81356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_81356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_81356 prefixEnd_81356 := by exact prefixLift 81356
  have htrace : WordTrace (prefixWord ++ tailWord_81356) baseStart_81356 baseEnd_81356 := by
    simpa [prefixWord, tailWord_81356, baseEnd_81356] using wordTrace_append hprefix tailTrace_81356
  have hstable : (prefixWord ++ tailWord_81356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81356).length < 2 ^ (prefixWord ++ tailWord_81356).sum := by decide
  have hdescent : baseEnd_81356 < baseStart_81356 := by decide
  rcases family_descends (prefixWord ++ tailWord_81356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81384 : List Nat := [2, 1, 4, 1, 1, 2, 1, 2, 8]
def baseStart_81384 : Nat := 118140960795 + 81384 * 2 ^ 59
def prefixEnd_81384 : Nat := 4983230072969 + 3 ^ 40 * 81384 * 2
def baseEnd_81384 : Nat := 9286468796803292983495

theorem tailTrace_81384 : CollatzResearch.WordTrace tailWord_81384 prefixEnd_81384 9286468796803292983495 := by
  unfold tailWord_81384
  simp only [CollatzResearch.WordTrace]
  refine ⟨1484159168583571062865603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1978878891444761417154137 1484159168583571062865603)
  ·
    refine ⟨2226238752875356594298405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1484159168583571062865603 2226238752875356594298405)
    ·
      refine ⟨417419766164129361430951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2226238752875356594298405 417419766164129361430951)
      ·
        refine ⟨626129649246194042146427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417419766164129361430951 626129649246194042146427)
        ·
          refine ⟨939194473869291063219641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 626129649246194042146427 939194473869291063219641)
          ·
            refine ⟨704395855401968297414731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 939194473869291063219641 704395855401968297414731)
            ·
              refine ⟨1056593783102952446122097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 704395855401968297414731 1056593783102952446122097)
              ·
                refine ⟨792445337327214334591573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1056593783102952446122097 792445337327214334591573)
                ·
                  refine ⟨9286468796803292983495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 792445337327214334591573 9286468796803292983495)
                  ·
                    rfl

theorem cell22_81384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 8].length) (baseStart_81384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_81384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_81384 prefixEnd_81384 := by exact prefixLift 81384
  have htrace : WordTrace (prefixWord ++ tailWord_81384) baseStart_81384 baseEnd_81384 := by
    simpa [prefixWord, tailWord_81384, baseEnd_81384] using wordTrace_append hprefix tailTrace_81384
  have hstable : (prefixWord ++ tailWord_81384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81384).length < 2 ^ (prefixWord ++ tailWord_81384).sum := by decide
  have hdescent : baseEnd_81384 < baseStart_81384 := by decide
  rcases family_descends (prefixWord ++ tailWord_81384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81416 : List Nat := [2, 1, 3, 2, 1, 1, 5, 1, 1, 5]
def baseStart_81416 : Nat := 118140960795 + 81416 * 2 ^ 59
def prefixEnd_81416 : Nat := 4983230072969 + 3 ^ 40 * 81416 * 2
def baseEnd_81416 : Nat := 27870360644372462150387

theorem tailTrace_81416 : CollatzResearch.WordTrace tailWord_81416 prefixEnd_81416 27870360644372462150387 := by
  unfold tailWord_81416
  simp only [CollatzResearch.WordTrace]
  refine ⟨1484742736525605795448051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1979656982034141060597401 1484742736525605795448051)
  ·
    refine ⟨2227114104788408693172077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1484742736525605795448051 2227114104788408693172077)
    ·
      refine ⟨835167789295653259939529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2227114104788408693172077 835167789295653259939529)
      ·
        refine ⟨626375841971739944954647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 835167789295653259939529 626375841971739944954647)
        ·
          refine ⟨939563762957609917431971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 626375841971739944954647 939563762957609917431971)
          ·
            refine ⟨1409345644436414876147957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 939563762957609917431971 1409345644436414876147957)
            ·
              refine ⟨132126154165913894638871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1409345644436414876147957 132126154165913894638871)
              ·
                refine ⟨198189231248870841958307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132126154165913894638871 198189231248870841958307)
                ·
                  refine ⟨297283846873306262937461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 198189231248870841958307 297283846873306262937461)
                  ·
                    refine ⟨27870360644372462150387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 297283846873306262937461 27870360644372462150387)
                    ·
                      rfl

theorem cell22_81416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_81416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_81416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_81416 prefixEnd_81416 := by exact prefixLift 81416
  have htrace : WordTrace (prefixWord ++ tailWord_81416) baseStart_81416 baseEnd_81416 := by
    simpa [prefixWord, tailWord_81416, baseEnd_81416] using wordTrace_append hprefix tailTrace_81416
  have hstable : (prefixWord ++ tailWord_81416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81416).length < 2 ^ (prefixWord ++ tailWord_81416).sum := by decide
  have hdescent : baseEnd_81416 < baseStart_81416 := by decide
  rcases family_descends (prefixWord ++ tailWord_81416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81508 : List Nat := [2, 3, 1, 1, 2, 4, 2, 2, 5]
def baseStart_81508 : Nat := 118140960795 + 81508 * 2 ^ 59
def prefixEnd_81508 : Nat := 4983230072969 + 3 ^ 40 * 81508 * 2
def baseEnd_81508 : Nat := 9300618041504962950035

theorem tailTrace_81508 : CollatzResearch.WordTrace tailWord_81508 prefixEnd_81508 9300618041504962950035 := by
  unfold tailWord_81508
  simp only [CollatzResearch.WordTrace]
  refine ⟨1486420494358955651622589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1981893992478607535496785 1486420494358955651622589)
  ·
    refine ⟨557407685384608369358471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1486420494358955651622589 557407685384608369358471)
    ·
      refine ⟨836111528076912554037707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 557407685384608369358471 836111528076912554037707)
      ·
        refine ⟨1254167292115368831056561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 836111528076912554037707 1254167292115368831056561)
        ·
          refine ⟨940625469086526623292421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1254167292115368831056561 940625469086526623292421)
          ·
            refine ⟨176367275453723741867329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 940625469086526623292421 176367275453723741867329)
            ·
              refine ⟨132275456590292806400497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176367275453723741867329 132275456590292806400497)
              ·
                refine ⟨99206592442719604800373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132275456590292806400497 99206592442719604800373)
                ·
                  refine ⟨9300618041504962950035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 99206592442719604800373 9300618041504962950035)
                  ·
                    rfl

theorem cell22_81508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_81508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_81508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_81508 prefixEnd_81508 := by exact prefixLift 81508
  have htrace : WordTrace (prefixWord ++ tailWord_81508) baseStart_81508 baseEnd_81508 := by
    simpa [prefixWord, tailWord_81508, baseEnd_81508] using wordTrace_append hprefix tailTrace_81508
  have hstable : (prefixWord ++ tailWord_81508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81508).length < 2 ^ (prefixWord ++ tailWord_81508).sum := by decide
  have hdescent : baseEnd_81508 < baseStart_81508 := by decide
  rcases family_descends (prefixWord ++ tailWord_81508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81512 : List Nat := [2, 1, 4, 3, 1, 2, 1, 4, 1, 3]
def baseStart_81512 : Nat := 118140960795 + 81512 * 2 ^ 59
def prefixEnd_81512 : Nat := 4983230072969 + 3 ^ 40 * 81512 * 2
def baseEnd_81512 : Nat := 27903223406260211750093

theorem tailTrace_81512 : CollatzResearch.WordTrace tailWord_81512 prefixEnd_81512 27903223406260211750093 := by
  unfold tailWord_81512
  simp only [CollatzResearch.WordTrace]
  refine ⟨1486493440351709993195395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1981991253802279990927193 1486493440351709993195395)
  ·
    refine ⟨2229740160527564989793093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1486493440351709993195395 2229740160527564989793093)
    ·
      refine ⟨418076280098918435586205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2229740160527564989793093 418076280098918435586205)
      ·
        refine ⟨156778605037094413344827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 418076280098918435586205 156778605037094413344827)
        ·
          refine ⟨235167907555641620017241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156778605037094413344827 235167907555641620017241)
          ·
            refine ⟨176375930666731215012931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235167907555641620017241 176375930666731215012931)
            ·
              refine ⟨264563896000096822519397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176375930666731215012931 264563896000096822519397)
              ·
                refine ⟨49605730500018154222387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 264563896000096822519397 49605730500018154222387)
                ·
                  refine ⟨74408595750027231333581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49605730500018154222387 74408595750027231333581)
                  ·
                    refine ⟨27903223406260211750093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74408595750027231333581 27903223406260211750093)
                    ·
                      rfl

theorem cell22_81512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_81512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_81512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_81512 prefixEnd_81512 := by exact prefixLift 81512
  have htrace : WordTrace (prefixWord ++ tailWord_81512) baseStart_81512 baseEnd_81512 := by
    simpa [prefixWord, tailWord_81512, baseEnd_81512] using wordTrace_append hprefix tailTrace_81512
  have hstable : (prefixWord ++ tailWord_81512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81512).length < 2 ^ (prefixWord ++ tailWord_81512).sum := by decide
  have hdescent : baseEnd_81512 < baseStart_81512 := by decide
  rcases family_descends (prefixWord ++ tailWord_81512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81536 : List Nat := [2, 1, 1, 2, 1, 4, 3, 2, 6]
def baseStart_81536 : Nat := 118140960795 + 81536 * 2 ^ 59
def prefixEnd_81536 : Nat := 4983230072969 + 3 ^ 40 * 81536 * 2
def baseEnd_81536 : Nat := 9303813032244049716673

theorem tailTrace_81536 : CollatzResearch.WordTrace tailWord_81536 prefixEnd_81536 9303813032244049716673 := by
  unfold tailWord_81536
  simp only [CollatzResearch.WordTrace]
  refine ⟨1486931116308236042632231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1982574821744314723509641 1486931116308236042632231)
  ·
    refine ⟨2230396674462354063948347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1486931116308236042632231 2230396674462354063948347)
    ·
      refine ⟨3345595011693531095922521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2230396674462354063948347 3345595011693531095922521)
      ·
        refine ⟨2509196258770148321941891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3345595011693531095922521 2509196258770148321941891)
        ·
          refine ⟨3763794388155222482912837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2509196258770148321941891 3763794388155222482912837)
          ·
            refine ⟨705711447779104215546157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3763794388155222482912837 705711447779104215546157)
            ·
              refine ⟨264641792917164080829809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 705711447779104215546157 264641792917164080829809)
              ·
                refine ⟨198481344687873060622357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 264641792917164080829809 198481344687873060622357)
                ·
                  refine ⟨9303813032244049716673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 198481344687873060622357 9303813032244049716673)
                  ·
                    rfl

theorem cell22_81536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 6].length) (baseStart_81536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_81536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_81536 prefixEnd_81536 := by exact prefixLift 81536
  have htrace : WordTrace (prefixWord ++ tailWord_81536) baseStart_81536 baseEnd_81536 := by
    simpa [prefixWord, tailWord_81536, baseEnd_81536] using wordTrace_append hprefix tailTrace_81536
  have hstable : (prefixWord ++ tailWord_81536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81536).length < 2 ^ (prefixWord ++ tailWord_81536).sum := by decide
  have hdescent : baseEnd_81536 < baseStart_81536 := by decide
  rcases family_descends (prefixWord ++ tailWord_81536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81598 : List Nat := [4, 2, 1, 1, 2, 3, 1, 8]
def baseStart_81598 : Nat := 118140960795 + 81598 * 2 ^ 59
def prefixEnd_81598 : Nat := 4983230072969 + 3 ^ 40 * 81598 * 2
def baseEnd_81598 : Nat := 3103629218198294899981

theorem tailTrace_81598 : CollatzResearch.WordTrace tailWord_81598 prefixEnd_81598 3103629218198294899981 := by
  unfold tailWord_81598
  simp only [CollatzResearch.WordTrace]
  refine ⟨372015444798982084252681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1984082372261237782680965 372015444798982084252681)
  ·
    refine ⟨279011583599236563189511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 372015444798982084252681 279011583599236563189511)
    ·
      refine ⟨418517375398854844784267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279011583599236563189511 418517375398854844784267)
      ·
        refine ⟨627776063098282267176401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 418517375398854844784267 627776063098282267176401)
        ·
          refine ⟨470832047323711700382301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 627776063098282267176401 470832047323711700382301)
          ·
            refine ⟨176562017746391887643363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 470832047323711700382301 176562017746391887643363)
            ·
              refine ⟨264843026619587831465045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176562017746391887643363 264843026619587831465045)
              ·
                refine ⟨3103629218198294899981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 264843026619587831465045 3103629218198294899981)
                ·
                  rfl

theorem cell22_81598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 8].length) (baseStart_81598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_81598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_81598 prefixEnd_81598 := by exact prefixLift 81598
  have htrace : WordTrace (prefixWord ++ tailWord_81598) baseStart_81598 baseEnd_81598 := by
    simpa [prefixWord, tailWord_81598, baseEnd_81598] using wordTrace_append hprefix tailTrace_81598
  have hstable : (prefixWord ++ tailWord_81598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81598).length < 2 ^ (prefixWord ++ tailWord_81598).sum := by decide
  have hdescent : baseEnd_81598 < baseStart_81598 := by decide
  rcases family_descends (prefixWord ++ tailWord_81598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81641 : List Nat := [1, 2, 1, 1, 1, 2, 3, 3, 1, 7]
def baseStart_81641 : Nat := 118140960795 + 81641 * 2 ^ 59
def prefixEnd_81641 : Nat := 4983230072969 + 3 ^ 40 * 81641 * 2
def baseEnd_81641 : Nat := 27947382742546875274697

theorem tailTrace_81641 : CollatzResearch.WordTrace tailWord_81641 prefixEnd_81641 27947382742546875274697 := by
  unfold tailWord_81641
  simp only [CollatzResearch.WordTrace]
  refine ⟨2977691897236075017836777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1985127931490716678557851 2977691897236075017836777)
  ·
    refine ⟨2233268922927056263377583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2977691897236075017836777 2233268922927056263377583)
    ·
      refine ⟨3349903384390584395066375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2233268922927056263377583 3349903384390584395066375)
      ·
        refine ⟨5024855076585876592599563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3349903384390584395066375 5024855076585876592599563)
        ·
          refine ⟨7537282614878814888899345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5024855076585876592599563 7537282614878814888899345)
          ·
            refine ⟨5652961961159111166674509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7537282614878814888899345 5652961961159111166674509)
            ·
              refine ⟨2119860735434666687502941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5652961961159111166674509 2119860735434666687502941)
              ·
                refine ⟨794947775788000007813603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2119860735434666687502941 794947775788000007813603)
                ·
                  refine ⟨1192421663682000011720405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 794947775788000007813603 1192421663682000011720405)
                  ·
                    refine ⟨27947382742546875274697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1192421663682000011720405 27947382742546875274697)
                    ·
                      rfl

theorem cell22_81641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 7].length) (baseStart_81641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_81641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_81641 prefixEnd_81641 := by exact prefixLift 81641
  have htrace : WordTrace (prefixWord ++ tailWord_81641) baseStart_81641 baseEnd_81641 := by
    simpa [prefixWord, tailWord_81641, baseEnd_81641] using wordTrace_append hprefix tailTrace_81641
  have hstable : (prefixWord ++ tailWord_81641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81641).length < 2 ^ (prefixWord ++ tailWord_81641).sum := by decide
  have hdescent : baseEnd_81641 < baseStart_81641 := by decide
  rcases family_descends (prefixWord ++ tailWord_81641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81670 : List Nat := [6, 2, 2, 1, 1, 1, 2, 2, 2, 3]
def baseStart_81670 : Nat := 118140960795 + 81670 * 2 ^ 59
def prefixEnd_81670 : Nat := 4983230072969 + 3 ^ 40 * 81670 * 2
def baseEnd_81670 : Nat := 27957310035200466299609

theorem tailTrace_81670 : CollatzResearch.WordTrace tailWord_81670 prefixEnd_81670 27957310035200466299609 := by
  unfold tailWord_81670
  simp only [CollatzResearch.WordTrace]
  refine ⟨93085925441594155332577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1985833076087341980428309 93085925441594155332577)
  ·
    refine ⟨69814444081195616499433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 93085925441594155332577 69814444081195616499433)
    ·
      refine ⟨52360833060896712374575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69814444081195616499433 52360833060896712374575)
      ·
        refine ⟨78541249591345068561863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52360833060896712374575 78541249591345068561863)
        ·
          refine ⟨117811874387017602842795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78541249591345068561863 117811874387017602842795)
          ·
            refine ⟨176717811580526404264193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117811874387017602842795 176717811580526404264193)
            ·
              refine ⟨132538358685394803198145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176717811580526404264193 132538358685394803198145)
              ·
                refine ⟨99403769014046102398609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132538358685394803198145 99403769014046102398609)
                ·
                  refine ⟨74552826760534576798957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99403769014046102398609 74552826760534576798957)
                  ·
                    refine ⟨27957310035200466299609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74552826760534576798957 27957310035200466299609)
                    ·
                      rfl

theorem cell22_81670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_81670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_81670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_81670 prefixEnd_81670 := by exact prefixLift 81670
  have htrace : WordTrace (prefixWord ++ tailWord_81670) baseStart_81670 baseEnd_81670 := by
    simpa [prefixWord, tailWord_81670, baseEnd_81670] using wordTrace_append hprefix tailTrace_81670
  have hstable : (prefixWord ++ tailWord_81670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81670).length < 2 ^ (prefixWord ++ tailWord_81670).sum := by decide
  have hdescent : baseEnd_81670 < baseStart_81670 := by decide
  rcases family_descends (prefixWord ++ tailWord_81670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81722 : List Nat := [3, 1, 1, 1, 5, 2, 2, 3, 4]
def baseStart_81722 : Nat := 118140960795 + 81722 * 2 ^ 59
def prefixEnd_81722 : Nat := 4983230072969 + 3 ^ 40 * 81722 * 2
def baseEnd_81722 : Nat := 9325036899296554666483

theorem tailTrace_81722 : CollatzResearch.WordTrace tailWord_81722 prefixEnd_81722 9325036899296554666483 := by
  unfold tailWord_81722
  simp only [CollatzResearch.WordTrace]
  refine ⟨745161552485656462883855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1987097473295083901023613 745161552485656462883855)
  ·
    refine ⟨1117742328728484694325783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 745161552485656462883855 1117742328728484694325783)
    ·
      refine ⟨1676613493092727041488675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1117742328728484694325783 1676613493092727041488675)
      ·
        refine ⟨2514920239639090562233013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1676613493092727041488675 2514920239639090562233013)
        ·
          refine ⟨235773772466164740209345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2514920239639090562233013 235773772466164740209345)
          ·
            refine ⟨176830329349623555157009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235773772466164740209345 176830329349623555157009)
            ·
              refine ⟨132622747012217666367757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176830329349623555157009 132622747012217666367757)
              ·
                refine ⟨49733530129581624887909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132622747012217666367757 49733530129581624887909)
                ·
                  refine ⟨9325036899296554666483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49733530129581624887909 9325036899296554666483)
                  ·
                    rfl

theorem cell22_81722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 3, 4].length) (baseStart_81722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_81722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_81722 prefixEnd_81722 := by exact prefixLift 81722
  have htrace : WordTrace (prefixWord ++ tailWord_81722) baseStart_81722 baseEnd_81722 := by
    simpa [prefixWord, tailWord_81722, baseEnd_81722] using wordTrace_append hprefix tailTrace_81722
  have hstable : (prefixWord ++ tailWord_81722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81722).length < 2 ^ (prefixWord ++ tailWord_81722).sum := by decide
  have hdescent : baseEnd_81722 < baseStart_81722 := by decide
  rcases family_descends (prefixWord ++ tailWord_81722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81799 : List Nat := [1, 1, 4, 2, 4, 2, 1, 1, 3, 3]
def baseStart_81799 : Nat := 118140960795 + 81799 * 2 ^ 59
def prefixEnd_81799 : Nat := 4983230072969 + 3 ^ 40 * 81799 * 2
def baseEnd_81799 : Nat := 28001469371487129824213

theorem tailTrace_81799 : CollatzResearch.WordTrace tailWord_81799 prefixEnd_81799 28001469371487129824213 := by
  unfold tailWord_81799
  simp only [CollatzResearch.WordTrace]
  refine ⟨2983454630663668002088451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1988969753775778668058967 2983454630663668002088451)
  ·
    refine ⟨4475181945995502003132677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2983454630663668002088451 4475181945995502003132677)
    ·
      refine ⟨839096614874156625587377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4475181945995502003132677 839096614874156625587377)
      ·
        refine ⟨629322461155617469190533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 839096614874156625587377 629322461155617469190533)
        ·
          refine ⟨117997961466678275473225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 629322461155617469190533 117997961466678275473225)
          ·
            refine ⟨88498471100008706604919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117997961466678275473225 88498471100008706604919)
            ·
              refine ⟨132747706650013059907379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88498471100008706604919 132747706650013059907379)
              ·
                refine ⟨199121559975019589861069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132747706650013059907379 199121559975019589861069)
                ·
                  refine ⟨74670584990632346197901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 199121559975019589861069 74670584990632346197901)
                  ·
                    refine ⟨28001469371487129824213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74670584990632346197901 28001469371487129824213)
                    ·
                      rfl

theorem cell22_81799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 3, 3].length) (baseStart_81799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_81799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_81799 prefixEnd_81799 := by exact prefixLift 81799
  have htrace : WordTrace (prefixWord ++ tailWord_81799) baseStart_81799 baseEnd_81799 := by
    simpa [prefixWord, tailWord_81799, baseEnd_81799] using wordTrace_append hprefix tailTrace_81799
  have hstable : (prefixWord ++ tailWord_81799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81799).length < 2 ^ (prefixWord ++ tailWord_81799).sum := by decide
  have hdescent : baseEnd_81799 < baseStart_81799 := by decide
  rcases family_descends (prefixWord ++ tailWord_81799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81812 : List Nat := [2, 4, 2, 1, 1, 3, 1, 3, 5]
def baseStart_81812 : Nat := 118140960795 + 81812 * 2 ^ 59
def prefixEnd_81812 : Nat := 4983230072969 + 3 ^ 40 * 81812 * 2
def baseEnd_81812 : Nat := 9335306512386476416391

theorem tailTrace_81812 : CollatzResearch.WordTrace tailWord_81812 prefixEnd_81812 9335306512386476416391 := by
  unfold tailWord_81812
  simp only [CollatzResearch.WordTrace]
  refine ⟨1491964389808285611155845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1989285853077714148207793 1491964389808285611155845)
  ·
    refine ⟨279743323089053552091721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1491964389808285611155845 279743323089053552091721)
    ·
      refine ⟨209807492316790164068791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279743323089053552091721 209807492316790164068791)
      ·
        refine ⟨314711238475185246103187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209807492316790164068791 314711238475185246103187)
        ·
          refine ⟨472066857712777869154781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314711238475185246103187 472066857712777869154781)
          ·
            refine ⟨177025071642291700933043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 472066857712777869154781 177025071642291700933043)
            ·
              refine ⟨265537607463437551399565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177025071642291700933043 265537607463437551399565)
              ·
                refine ⟨99576602798789081774837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 265537607463437551399565 99576602798789081774837)
                ·
                  refine ⟨9335306512386476416391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 99576602798789081774837 9335306512386476416391)
                  ·
                    rfl

theorem cell22_81812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_81812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_81812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_81812 prefixEnd_81812 := by exact prefixLift 81812
  have htrace : WordTrace (prefixWord ++ tailWord_81812) baseStart_81812 baseEnd_81812 := by
    simpa [prefixWord, tailWord_81812, baseEnd_81812] using wordTrace_append hprefix tailTrace_81812
  have hstable : (prefixWord ++ tailWord_81812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81812).length < 2 ^ (prefixWord ++ tailWord_81812).sum := by decide
  have hdescent : baseEnd_81812 < baseStart_81812 := by decide
  rcases family_descends (prefixWord ++ tailWord_81812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81870 : List Nat := [4, 1, 1, 1, 2, 2, 2, 2, 1, 6]
def baseStart_81870 : Nat := 118140960795 + 81870 * 2 ^ 59
def prefixEnd_81870 : Nat := 4983230072969 + 3 ^ 40 * 81870 * 2
def baseEnd_81870 : Nat := 28025774122466611298995

theorem tailTrace_81870 : CollatzResearch.WordTrace tailWord_81870 prefixEnd_81870 28025774122466611298995 := by
  unfold tailWord_81870
  simp only [CollatzResearch.WordTrace]
  refine ⟨373255526675805890990383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1990696142270964751948709 373255526675805890990383)
  ·
    refine ⟨559883290013708836485575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 373255526675805890990383 559883290013708836485575)
    ·
      refine ⟨839824935020563254728363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 559883290013708836485575 839824935020563254728363)
      ·
        refine ⟨1259737402530844882092545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 839824935020563254728363 1259737402530844882092545)
        ·
          refine ⟨944803051898133661569409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1259737402530844882092545 944803051898133661569409)
          ·
            refine ⟨708602288923600246177057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 944803051898133661569409 708602288923600246177057)
            ·
              refine ⟨531451716692700184632793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 708602288923600246177057 531451716692700184632793)
              ·
                refine ⟨398588787519525138474595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 531451716692700184632793 398588787519525138474595)
                ·
                  refine ⟨597883181279287707711893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 398588787519525138474595 597883181279287707711893)
                  ·
                    refine ⟨28025774122466611298995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 597883181279287707711893 28025774122466611298995)
                    ·
                      rfl

theorem cell22_81870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_81870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_81870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_81870 prefixEnd_81870 := by exact prefixLift 81870
  have htrace : WordTrace (prefixWord ++ tailWord_81870) baseStart_81870 baseEnd_81870 := by
    simpa [prefixWord, tailWord_81870, baseEnd_81870] using wordTrace_append hprefix tailTrace_81870
  have hstable : (prefixWord ++ tailWord_81870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81870).length < 2 ^ (prefixWord ++ tailWord_81870).sum := by decide
  have hdescent : baseEnd_81870 < baseStart_81870 := by decide
  rcases family_descends (prefixWord ++ tailWord_81870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81872 : List Nat := [2, 1, 1, 1, 1, 2, 6, 3, 2, 3]
def baseStart_81872 : Nat := 118140960795 + 81872 * 2 ^ 59
def prefixEnd_81872 : Nat := 4983230072969 + 3 ^ 40 * 81872 * 2
def baseEnd_81872 : Nat := 28026458763339272748989

theorem tailTrace_81872 : CollatzResearch.WordTrace tailWord_81872 prefixEnd_81872 28026458763339272748989 := by
  unfold tailWord_81872
  simp only [CollatzResearch.WordTrace]
  refine ⟨1493058579699600734747935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1990744772932800979663913 1493058579699600734747935)
  ·
    refine ⟨2239587869549401102121903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1493058579699600734747935 2239587869549401102121903)
    ·
      refine ⟨3359381804324101653182855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2239587869549401102121903 3359381804324101653182855)
      ·
        refine ⟨5039072706486152479774283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3359381804324101653182855 5039072706486152479774283)
        ·
          refine ⟨7558609059729228719661425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5039072706486152479774283 7558609059729228719661425)
          ·
            refine ⟨5668956794796921539746069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7558609059729228719661425 5668956794796921539746069)
            ·
              refine ⟨265732349756105697175597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5668956794796921539746069 265732349756105697175597)
              ·
                refine ⟨99649631158539636440849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 265732349756105697175597 99649631158539636440849)
                ·
                  refine ⟨74737223368904727330637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99649631158539636440849 74737223368904727330637)
                  ·
                    refine ⟨28026458763339272748989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74737223368904727330637 28026458763339272748989)
                    ·
                      rfl

theorem cell22_81872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 2, 3].length) (baseStart_81872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_81872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_81872 prefixEnd_81872 := by exact prefixLift 81872
  have htrace : WordTrace (prefixWord ++ tailWord_81872) baseStart_81872 baseEnd_81872 := by
    simpa [prefixWord, tailWord_81872, baseEnd_81872] using wordTrace_append hprefix tailTrace_81872
  have hstable : (prefixWord ++ tailWord_81872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81872).length < 2 ^ (prefixWord ++ tailWord_81872).sum := by decide
  have hdescent : baseEnd_81872 < baseStart_81872 := by decide
  rcases family_descends (prefixWord ++ tailWord_81872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81887 : List Nat := [1, 1, 2, 3, 4, 1, 3, 1, 2, 4]
def baseStart_81887 : Nat := 118140960795 + 81887 * 2 ^ 59
def prefixEnd_81887 : Nat := 4983230072969 + 3 ^ 40 * 81887 * 2
def baseEnd_81887 : Nat := 28031593569884233623943

theorem tailTrace_81887 : CollatzResearch.WordTrace tailWord_81887 prefixEnd_81887 28031593569884233623943 := by
  unfold tailWord_81887
  simp only [CollatzResearch.WordTrace]
  refine ⟨2986664254344859031291915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1991109502896572687527943 2986664254344859031291915)
  ·
    refine ⟨4479996381517288546937873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2986664254344859031291915 4479996381517288546937873)
    ·
      refine ⟨3359997286137966410203405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4479996381517288546937873 3359997286137966410203405)
      ·
        refine ⟨1259998982301737403826277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3359997286137966410203405 1259998982301737403826277)
        ·
          refine ⟨236249809181575763217427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1259998982301737403826277 236249809181575763217427)
          ·
            refine ⟨354374713772363644826141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236249809181575763217427 354374713772363644826141)
            ·
              refine ⟨132890517664636366809803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 354374713772363644826141 132890517664636366809803)
              ·
                refine ⟨199335776496954550214705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132890517664636366809803 199335776496954550214705)
                ·
                  refine ⟨149501832372715912661029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 199335776496954550214705 149501832372715912661029)
                  ·
                    refine ⟨28031593569884233623943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 149501832372715912661029 28031593569884233623943)
                    ·
                      rfl

theorem cell22_81887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 1, 2, 4].length) (baseStart_81887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_81887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_81887 prefixEnd_81887 := by exact prefixLift 81887
  have htrace : WordTrace (prefixWord ++ tailWord_81887) baseStart_81887 baseEnd_81887 := by
    simpa [prefixWord, tailWord_81887, baseEnd_81887] using wordTrace_append hprefix tailTrace_81887
  have hstable : (prefixWord ++ tailWord_81887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81887).length < 2 ^ (prefixWord ++ tailWord_81887).sum := by decide
  have hdescent : baseEnd_81887 < baseStart_81887 := by decide
  rcases family_descends (prefixWord ++ tailWord_81887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81917 : List Nat := [1, 4, 1, 1, 1, 2, 3, 3, 3, 3]
def baseStart_81917 : Nat := 118140960795 + 81917 * 2 ^ 59
def prefixEnd_81917 : Nat := 4983230072969 + 3 ^ 40 * 81917 * 2
def baseEnd_81917 : Nat := 28041863182974155373851

theorem tailTrace_81917 : CollatzResearch.WordTrace tailWord_81917 prefixEnd_81917 28041863182974155373851 := by
  unfold tailWord_81917
  simp only [CollatzResearch.WordTrace]
  refine ⟨2987758444236174154884005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1991838962824116103256003 2987758444236174154884005)
  ·
    refine ⟨560204708294282654040751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2987758444236174154884005 560204708294282654040751)
    ·
      refine ⟨840307062441423981061127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 560204708294282654040751 840307062441423981061127)
      ·
        refine ⟨1260460593662135971591691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 840307062441423981061127 1260460593662135971591691)
        ·
          refine ⟨1890690890493203957387537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1260460593662135971591691 1890690890493203957387537)
          ·
            refine ⟨1418018167869902968040653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1890690890493203957387537 1418018167869902968040653)
            ·
              refine ⟨531756812951213613015245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1418018167869902968040653 531756812951213613015245)
              ·
                refine ⟨199408804856705104880717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 531756812951213613015245 199408804856705104880717)
                ·
                  refine ⟨74778301821264414330269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 199408804856705104880717 74778301821264414330269)
                  ·
                    refine ⟨28041863182974155373851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74778301821264414330269 28041863182974155373851)
                    ·
                      rfl

theorem cell22_81917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 3, 3].length) (baseStart_81917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_81917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_81917 prefixEnd_81917 := by exact prefixLift 81917
  have htrace : WordTrace (prefixWord ++ tailWord_81917) baseStart_81917 baseEnd_81917 := by
    simpa [prefixWord, tailWord_81917, baseEnd_81917] using wordTrace_append hprefix tailTrace_81917
  have hstable : (prefixWord ++ tailWord_81917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81917).length < 2 ^ (prefixWord ++ tailWord_81917).sum := by decide
  have hdescent : baseEnd_81917 < baseStart_81917 := by decide
  rcases family_descends (prefixWord ++ tailWord_81917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82007 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 6, 3]
def baseStart_82007 : Nat := 118140960795 + 82007 * 2 ^ 59
def prefixEnd_82007 : Nat := 4983230072969 + 3 ^ 40 * 82007 * 2
def baseEnd_82007 : Nat := 28072672022243920623575

theorem tailTrace_82007 : CollatzResearch.WordTrace tailWord_82007 prefixEnd_82007 28072672022243920623575 := by
  unfold tailWord_82007
  simp only [CollatzResearch.WordTrace]
  refine ⟨2991041013910119525660275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1994027342606746350440183 2991041013910119525660275)
  ·
    refine ⟨4486561520865179288490413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2991041013910119525660275 4486561520865179288490413)
    ·
      refine ⟨1682460570324442233183905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4486561520865179288490413 1682460570324442233183905)
      ·
        refine ⟨1261845427743331674887929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1682460570324442233183905 1261845427743331674887929)
        ·
          refine ⟨946384070807498756165947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1261845427743331674887929 946384070807498756165947)
          ·
            refine ⟨1419576106211248134248921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 946384070807498756165947 1419576106211248134248921)
            ·
              refine ⟨1064682079658436100686691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1419576106211248134248921 1064682079658436100686691)
              ·
                refine ⟨1597023119487654151030037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1064682079658436100686691 1597023119487654151030037)
                ·
                  refine ⟨74860458725983788329533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1597023119487654151030037 74860458725983788329533)
                  ·
                    refine ⟨28072672022243920623575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74860458725983788329533 28072672022243920623575)
                    ·
                      rfl

theorem cell22_82007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 6, 3].length) (baseStart_82007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_82007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_82007 prefixEnd_82007 := by exact prefixLift 82007
  have htrace : WordTrace (prefixWord ++ tailWord_82007) baseStart_82007 baseEnd_82007 := by
    simpa [prefixWord, tailWord_82007, baseEnd_82007] using wordTrace_append hprefix tailTrace_82007
  have hstable : (prefixWord ++ tailWord_82007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82007).length < 2 ^ (prefixWord ++ tailWord_82007).sum := by decide
  have hdescent : baseEnd_82007 < baseStart_82007 := by decide
  rcases family_descends (prefixWord ++ tailWord_82007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82026 : List Nat := [3, 1, 3, 2, 3, 1, 1, 4, 4]
def baseStart_82026 : Nat := 118140960795 + 82026 * 2 ^ 59
def prefixEnd_82026 : Nat := 4983230072969 + 3 ^ 40 * 82026 * 2
def baseEnd_82026 : Nat := 9359725370178068132839

theorem tailTrace_82026 : CollatzResearch.WordTrace tailWord_82026 prefixEnd_82026 9359725370178068132839 := by
  unfold tailWord_82026
  simp only [CollatzResearch.WordTrace]
  refine ⟨747933500210321442650483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1994489333894190513734621 747933500210321442650483)
  ·
    refine ⟨1121900250315482163975725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 747933500210321442650483 1121900250315482163975725)
    ·
      refine ⟨420712593868305811490897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1121900250315482163975725 420712593868305811490897)
      ·
        refine ⟨315534445401229358618173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 420712593868305811490897 315534445401229358618173)
        ·
          refine ⟨118325417025461009481815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 315534445401229358618173 118325417025461009481815)
          ·
            refine ⟨177488125538191514222723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118325417025461009481815 177488125538191514222723)
            ·
              refine ⟨266232188307287271334085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177488125538191514222723 266232188307287271334085)
              ·
                refine ⟨49918535307616363375141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 266232188307287271334085 49918535307616363375141)
                ·
                  refine ⟨9359725370178068132839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49918535307616363375141 9359725370178068132839)
                  ·
                    rfl

theorem cell22_82026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 4, 4].length) (baseStart_82026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_82026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_82026 prefixEnd_82026 := by exact prefixLift 82026
  have htrace : WordTrace (prefixWord ++ tailWord_82026) baseStart_82026 baseEnd_82026 := by
    simpa [prefixWord, tailWord_82026, baseEnd_82026] using wordTrace_append hprefix tailTrace_82026
  have hstable : (prefixWord ++ tailWord_82026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82026).length < 2 ^ (prefixWord ++ tailWord_82026).sum := by decide
  have hdescent : baseEnd_82026 < baseStart_82026 := by decide
  rcases family_descends (prefixWord ++ tailWord_82026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82056 : List Nat := [2, 1, 3, 4, 1, 3, 1, 1, 2, 4]
def baseStart_82056 : Nat := 118140960795 + 82056 * 2 ^ 59
def prefixEnd_82056 : Nat := 4983230072969 + 3 ^ 40 * 82056 * 2
def baseEnd_82056 : Nat := 28089445723624126148425

theorem tailTrace_82056 : CollatzResearch.WordTrace tailWord_82056 prefixEnd_82056 28089445723624126148425 := by
  unfold tailWord_82056
  simp only [CollatzResearch.WordTrace]
  refine ⟨1496414095366300447097011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1995218793821733929462681 1496414095366300447097011)
  ·
    refine ⟨2244621143049450670645517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1496414095366300447097011 2244621143049450670645517)
    ·
      refine ⟨841732928643544001492069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2244621143049450670645517 841732928643544001492069)
      ·
        refine ⟨157824924120664500279763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 841732928643544001492069 157824924120664500279763)
        ·
          refine ⟨236737386180996750419645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157824924120664500279763 236737386180996750419645)
          ·
            refine ⟨88776519817873781407367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 236737386180996750419645 88776519817873781407367)
            ·
              refine ⟨133164779726810672111051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88776519817873781407367 133164779726810672111051)
              ·
                refine ⟨199747169590216008166577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133164779726810672111051 199747169590216008166577)
                ·
                  refine ⟨149810377192662006124933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 199747169590216008166577 149810377192662006124933)
                  ·
                    refine ⟨28089445723624126148425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 149810377192662006124933 28089445723624126148425)
                    ·
                      rfl

theorem cell22_82056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 2, 4].length) (baseStart_82056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_82056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_82056 prefixEnd_82056 := by exact prefixLift 82056
  have htrace : WordTrace (prefixWord ++ tailWord_82056) baseStart_82056 baseEnd_82056 := by
    simpa [prefixWord, tailWord_82056, baseEnd_82056] using wordTrace_append hprefix tailTrace_82056
  have hstable : (prefixWord ++ tailWord_82056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82056).length < 2 ^ (prefixWord ++ tailWord_82056).sum := by decide
  have hdescent : baseEnd_82056 < baseStart_82056 := by decide
  rcases family_descends (prefixWord ++ tailWord_82056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82129 : List Nat := [1, 2, 2, 1, 2, 2, 4, 3, 1, 4]
def baseStart_82129 : Nat := 118140960795 + 82129 * 2 ^ 59
def prefixEnd_82129 : Nat := 4983230072969 + 3 ^ 40 * 82129 * 2
def baseEnd_82129 : Nat := 28114435115476269073201

theorem tailTrace_82129 : CollatzResearch.WordTrace tailWord_82129 prefixEnd_82129 28114435115476269073201 := by
  unfold tailWord_82129
  simp only [CollatzResearch.WordTrace]
  refine ⟨2995490719468134361601441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1996993812978756241067627 2995490719468134361601441)
  ·
    refine ⟨2246618039601100771201081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2995490719468134361601441 2246618039601100771201081)
    ·
      refine ⟨1684963529700825578400811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2246618039601100771201081 1684963529700825578400811)
      ·
        refine ⟨2527445294551238367601217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1684963529700825578400811 2527445294551238367601217)
        ·
          refine ⟨1895583970913428775700913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2527445294551238367601217 1895583970913428775700913)
          ·
            refine ⟨1421687978185071581775685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1895583970913428775700913 1421687978185071581775685)
            ·
              refine ⟨266566495909700921582941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1421687978185071581775685 266566495909700921582941)
              ·
                refine ⟨99962435966137845593603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 266566495909700921582941 99962435966137845593603)
                ·
                  refine ⟨149943653949206768390405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99962435966137845593603 149943653949206768390405)
                  ·
                    refine ⟨28114435115476269073201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 149943653949206768390405 28114435115476269073201)
                    ·
                      rfl

theorem cell22_82129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 4].length) (baseStart_82129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_82129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_82129 prefixEnd_82129 := by exact prefixLift 82129
  have htrace : WordTrace (prefixWord ++ tailWord_82129) baseStart_82129 baseEnd_82129 := by
    simpa [prefixWord, tailWord_82129, baseEnd_82129] using wordTrace_append hprefix tailTrace_82129
  have hstable : (prefixWord ++ tailWord_82129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82129).length < 2 ^ (prefixWord ++ tailWord_82129).sum := by decide
  have hdescent : baseEnd_82129 < baseStart_82129 := by decide
  rcases family_descends (prefixWord ++ tailWord_82129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82264 : List Nat := [2, 1, 2, 2, 1, 1, 2, 4, 3, 4]
def baseStart_82264 : Nat := 118140960795 + 82264 * 2 ^ 59
def prefixEnd_82264 : Nat := 4983230072969 + 3 ^ 40 * 82264 * 2
def baseEnd_82264 : Nat := 28160648374380916947787

theorem tailTrace_82264 : CollatzResearch.WordTrace tailWord_82264 prefixEnd_82264 28160648374380916947787 := by
  unfold tailWord_82264
  simp only [CollatzResearch.WordTrace]
  refine ⟨1500207286989526208882923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2000276382652701611843897 1500207286989526208882923)
  ·
    refine ⟨2250310930484289313324385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1500207286989526208882923 2250310930484289313324385)
    ·
      refine ⟨1687733197863216984993289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2250310930484289313324385 1687733197863216984993289)
      ·
        refine ⟨1265799898397412738744967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1687733197863216984993289 1265799898397412738744967)
        ·
          refine ⟨1898699847596119108117451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1265799898397412738744967 1898699847596119108117451)
          ·
            refine ⟨2848049771394178662176177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1898699847596119108117451 2848049771394178662176177)
            ·
              refine ⟨2136037328545633996632133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2848049771394178662176177 2136037328545633996632133)
              ·
                refine ⟨400506999102306374368525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2136037328545633996632133 400506999102306374368525)
                ·
                  refine ⟨150190124663364890388197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 400506999102306374368525 150190124663364890388197)
                  ·
                    refine ⟨28160648374380916947787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 150190124663364890388197 28160648374380916947787)
                    ·
                      rfl

theorem cell22_82264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 4, 3, 4].length) (baseStart_82264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_82264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_82264 prefixEnd_82264 := by exact prefixLift 82264
  have htrace : WordTrace (prefixWord ++ tailWord_82264) baseStart_82264 baseEnd_82264 := by
    simpa [prefixWord, tailWord_82264, baseEnd_82264] using wordTrace_append hprefix tailTrace_82264
  have hstable : (prefixWord ++ tailWord_82264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82264).length < 2 ^ (prefixWord ++ tailWord_82264).sum := by decide
  have hdescent : baseEnd_82264 < baseStart_82264 := by decide
  rcases family_descends (prefixWord ++ tailWord_82264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82281 : List Nat := [1, 2, 1, 1, 1, 3, 6, 2, 1, 4]
def baseStart_82281 : Nat := 118140960795 + 82281 * 2 ^ 59
def prefixEnd_82281 : Nat := 4983230072969 + 3 ^ 40 * 82281 * 2
def baseEnd_82281 : Nat := 28166467821798539272735

theorem tailTrace_82281 : CollatzResearch.WordTrace tailWord_82281 prefixEnd_82281 28166467821798539272735 := by
  unfold tailWord_82281
  simp only [CollatzResearch.WordTrace]
  refine ⟨3001034614917464321134697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2000689743278309547423131 3001034614917464321134697)
  ·
    refine ⟨2250775961188098240851023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3001034614917464321134697 2250775961188098240851023)
    ·
      refine ⟨3376163941782147361276535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2250775961188098240851023 3376163941782147361276535)
      ·
        refine ⟨5064245912673221041914803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3376163941782147361276535 5064245912673221041914803)
        ·
          refine ⟨7596368869009831562872205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5064245912673221041914803 7596368869009831562872205)
          ·
            refine ⟨2848638325878686836077077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7596368869009831562872205 2848638325878686836077077)
            ·
              refine ⟨133529921525563445441113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2848638325878686836077077 133529921525563445441113)
              ·
                refine ⟨100147441144172584080835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133529921525563445441113 100147441144172584080835)
                ·
                  refine ⟨150221161716258876121253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 100147441144172584080835 150221161716258876121253)
                  ·
                    refine ⟨28166467821798539272735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 150221161716258876121253 28166467821798539272735)
                    ·
                      rfl

theorem cell22_82281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 2, 1, 4].length) (baseStart_82281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_82281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_82281 prefixEnd_82281 := by exact prefixLift 82281
  have htrace : WordTrace (prefixWord ++ tailWord_82281) baseStart_82281 baseEnd_82281 := by
    simpa [prefixWord, tailWord_82281, baseEnd_82281] using wordTrace_append hprefix tailTrace_82281
  have hstable : (prefixWord ++ tailWord_82281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82281).length < 2 ^ (prefixWord ++ tailWord_82281).sum := by decide
  have hdescent : baseEnd_82281 < baseStart_82281 := by decide
  rcases family_descends (prefixWord ++ tailWord_82281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82311 : List Nat := [1, 1, 4, 2, 2, 1, 1, 3, 4, 3]
def baseStart_82311 : Nat := 118140960795 + 82311 * 2 ^ 59
def prefixEnd_82311 : Nat := 4983230072969 + 3 ^ 40 * 82311 * 2
def baseEnd_82311 : Nat := 28176737434888461022643

theorem tailTrace_82311 : CollatzResearch.WordTrace tailWord_82311 prefixEnd_82311 28176737434888461022643 := by
  unfold tailWord_82311
  simp only [CollatzResearch.WordTrace]
  refine ⟨3002128804808779444726787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2001419203205852963151191 3002128804808779444726787)
  ·
    refine ⟨4503193207213169167090181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3002128804808779444726787 4503193207213169167090181)
    ·
      refine ⟨844348726352469218829409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4503193207213169167090181 844348726352469218829409)
      ·
        refine ⟨633261544764351914122057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 844348726352469218829409 633261544764351914122057)
        ·
          refine ⟨474946158573263935591543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 633261544764351914122057 474946158573263935591543)
          ·
            refine ⟨712419237859895903387315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 474946158573263935591543 712419237859895903387315)
            ·
              refine ⟨1068628856789843855080973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 712419237859895903387315 1068628856789843855080973)
              ·
                refine ⟨400735821296191445655365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1068628856789843855080973 400735821296191445655365)
                ·
                  refine ⟨75137966493035896060381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 400735821296191445655365 75137966493035896060381)
                  ·
                    refine ⟨28176737434888461022643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75137966493035896060381 28176737434888461022643)
                    ·
                      rfl

theorem cell22_82311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 4, 3].length) (baseStart_82311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_82311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_82311 prefixEnd_82311 := by exact prefixLift 82311
  have htrace : WordTrace (prefixWord ++ tailWord_82311) baseStart_82311 baseEnd_82311 := by
    simpa [prefixWord, tailWord_82311, baseEnd_82311] using wordTrace_append hprefix tailTrace_82311
  have hstable : (prefixWord ++ tailWord_82311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82311).length < 2 ^ (prefixWord ++ tailWord_82311).sum := by decide
  have hdescent : baseEnd_82311 < baseStart_82311 := by decide
  rcases family_descends (prefixWord ++ tailWord_82311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82343 : List Nat := [1, 1, 6, 1, 1, 3, 2, 1, 2, 4]
def baseStart_82343 : Nat := 118140960795 + 82343 * 2 ^ 59
def prefixEnd_82343 : Nat := 4983230072969 + 3 ^ 40 * 82343 * 2
def baseEnd_82343 : Nat := 28187691688851044222545

theorem tailTrace_82343 : CollatzResearch.WordTrace tailWord_82343 prefixEnd_82343 28187691688851044222545 := by
  unfold tailWord_82343
  simp only [CollatzResearch.WordTrace]
  refine ⟨3003295940692848909891683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2002197293795232606594455 3003295940692848909891683)
  ·
    refine ⟨4504943911039273364837525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3003295940692848909891683 4504943911039273364837525)
    ·
      refine ⟨211169245829965938976759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4504943911039273364837525 211169245829965938976759)
      ·
        refine ⟨316753868744948908465139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211169245829965938976759 316753868744948908465139)
        ·
          refine ⟨475130803117423362697709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316753868744948908465139 475130803117423362697709)
          ·
            refine ⟨178174051169033761011641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 475130803117423362697709 178174051169033761011641)
            ·
              refine ⟨133630538376775320758731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178174051169033761011641 133630538376775320758731)
              ·
                refine ⟨200445807565162981138097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133630538376775320758731 200445807565162981138097)
                ·
                  refine ⟨150334355673872235853573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 200445807565162981138097 150334355673872235853573)
                  ·
                    refine ⟨28187691688851044222545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 150334355673872235853573 28187691688851044222545)
                    ·
                      rfl

theorem cell22_82343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_82343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_82343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_82343 prefixEnd_82343 := by exact prefixLift 82343
  have htrace : WordTrace (prefixWord ++ tailWord_82343) baseStart_82343 baseEnd_82343 := by
    simpa [prefixWord, tailWord_82343, baseEnd_82343] using wordTrace_append hprefix tailTrace_82343
  have hstable : (prefixWord ++ tailWord_82343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82343).length < 2 ^ (prefixWord ++ tailWord_82343).sum := by decide
  have hdescent : baseEnd_82343 < baseStart_82343 := by decide
  rcases family_descends (prefixWord ++ tailWord_82343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82390 : List Nat := [5, 2, 1, 1, 1, 1, 3, 2, 3, 3]
def baseStart_82390 : Nat := 118140960795 + 82390 * 2 ^ 59
def prefixEnd_82390 : Nat := 4983230072969 + 3 ^ 40 * 82390 * 2
def baseEnd_82390 : Nat := 28203780749358588297401

theorem tailTrace_82390 : CollatzResearch.WordTrace tailWord_82390 prefixEnd_82390 28203780749358588297401 := by
  unfold tailWord_82390
  simp only [CollatzResearch.WordTrace]
  refine ⟨187813135720160996053289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2003340114348383957901749 187813135720160996053289)
  ·
    refine ⟨140859851790120747039967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 187813135720160996053289 140859851790120747039967)
    ·
      refine ⟨211289777685181120559951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140859851790120747039967 211289777685181120559951)
      ·
        refine ⟨316934666527771680839927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211289777685181120559951 316934666527771680839927)
        ·
          refine ⟨475401999791657521259891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316934666527771680839927 475401999791657521259891)
          ·
            refine ⟨713102999687486281889837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475401999791657521259891 713102999687486281889837)
            ·
              refine ⟨267413624882807355708689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 713102999687486281889837 267413624882807355708689)
              ·
                refine ⟨200560218662105516781517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 267413624882807355708689 200560218662105516781517)
                ·
                  refine ⟨75210081998289568793069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 200560218662105516781517 75210081998289568793069)
                  ·
                    refine ⟨28203780749358588297401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75210081998289568793069 28203780749358588297401)
                    ·
                      rfl

theorem cell22_82390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_82390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_82390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_82390 prefixEnd_82390 := by exact prefixLift 82390
  have htrace : WordTrace (prefixWord ++ tailWord_82390) baseStart_82390 baseEnd_82390 := by
    simpa [prefixWord, tailWord_82390, baseEnd_82390] using wordTrace_append hprefix tailTrace_82390
  have hstable : (prefixWord ++ tailWord_82390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82390).length < 2 ^ (prefixWord ++ tailWord_82390).sum := by decide
  have hdescent : baseEnd_82390 < baseStart_82390 := by decide
  rcases family_descends (prefixWord ++ tailWord_82390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82431 : List Nat := [1, 1, 2, 2, 1, 2, 6, 1, 6]
def baseStart_82431 : Nat := 118140960795 + 82431 * 2 ^ 59
def prefixEnd_82431 : Nat := 4983230072969 + 3 ^ 40 * 82431 * 2
def baseEnd_82431 : Nat := 9405938629082716007425

theorem tailTrace_82431 : CollatzResearch.WordTrace tailWord_82431 prefixEnd_82431 9405938629082716007425 := by
  unfold tailWord_82431
  simp only [CollatzResearch.WordTrace]
  refine ⟨3006505564374039939095147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2004337042916026626063431 3006505564374039939095147)
  ·
    refine ⟨4509758346561059908642721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3006505564374039939095147 4509758346561059908642721)
    ·
      refine ⟨3382318759920794931482041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4509758346561059908642721 3382318759920794931482041)
      ·
        refine ⟨2536739069940596198611531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3382318759920794931482041 2536739069940596198611531)
        ·
          refine ⟨3805108604910894297917297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2536739069940596198611531 3805108604910894297917297)
          ·
            refine ⟨2853831453683170723437973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3805108604910894297917297 2853831453683170723437973)
            ·
              refine ⟨133773349391398627661155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2853831453683170723437973 133773349391398627661155)
              ·
                refine ⟨200660024087097941491733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133773349391398627661155 200660024087097941491733)
                ·
                  refine ⟨9405938629082716007425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 200660024087097941491733 9405938629082716007425)
                  ·
                    rfl

theorem cell22_82431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 6].length) (baseStart_82431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_82431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_82431 prefixEnd_82431 := by exact prefixLift 82431
  have htrace : WordTrace (prefixWord ++ tailWord_82431) baseStart_82431 baseEnd_82431 := by
    simpa [prefixWord, tailWord_82431, baseEnd_82431] using wordTrace_append hprefix tailTrace_82431
  have hstable : (prefixWord ++ tailWord_82431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82431).length < 2 ^ (prefixWord ++ tailWord_82431).sum := by decide
  have hdescent : baseEnd_82431 < baseStart_82431 := by decide
  rcases family_descends (prefixWord ++ tailWord_82431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82493 : List Nat := [1, 4, 1, 3, 2, 2, 2, 7]
def baseStart_82493 : Nat := 118140960795 + 82493 * 2 ^ 59
def prefixEnd_82493 : Nat := 4983230072969 + 3 ^ 40 * 82493 * 2
def baseEnd_82493 : Nat := 3137671083811183663565

theorem tailTrace_82493 : CollatzResearch.WordTrace tailWord_82493 prefixEnd_82493 3137671083811183663565 := by
  unfold tailWord_82493
  simp only [CollatzResearch.WordTrace]
  refine ⟨3008766890149424527852133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2005844593432949685234755 3008766890149424527852133)
  ·
    refine ⟨564143791903017098972275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3008766890149424527852133 564143791903017098972275)
    ·
      refine ⟨846215687854525648458413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 564143791903017098972275 846215687854525648458413)
      ·
        refine ⟨317330882945447118171905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 846215687854525648458413 317330882945447118171905)
        ·
          refine ⟨237998162209085338628929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 317330882945447118171905 237998162209085338628929)
          ·
            refine ⟨178498621656814003971697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 237998162209085338628929 178498621656814003971697)
            ·
              refine ⟨133873966242610502978773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178498621656814003971697 133873966242610502978773)
              ·
                refine ⟨3137671083811183663565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 133873966242610502978773 3137671083811183663565)
                ·
                  rfl

theorem cell22_82493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 7].length) (baseStart_82493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_82493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_82493 prefixEnd_82493 := by exact prefixLift 82493
  have htrace : WordTrace (prefixWord ++ tailWord_82493) baseStart_82493 baseEnd_82493 := by
    simpa [prefixWord, tailWord_82493, baseEnd_82493] using wordTrace_append hprefix tailTrace_82493
  have hstable : (prefixWord ++ tailWord_82493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82493).length < 2 ^ (prefixWord ++ tailWord_82493).sum := by decide
  have hdescent : baseEnd_82493 < baseStart_82493 := by decide
  rcases family_descends (prefixWord ++ tailWord_82493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82497 : List Nat := [1, 2, 5, 1, 1, 2, 4, 1, 2, 3]
def baseStart_82497 : Nat := 118140960795 + 82497 * 2 ^ 59
def prefixEnd_82497 : Nat := 4983230072969 + 3 ^ 40 * 82497 * 2
def baseEnd_82497 : Nat := 28240409036045975872073

theorem tailTrace_82497 : CollatzResearch.WordTrace tailWord_82497 prefixEnd_82497 28240409036045975872073 := by
  unfold tailWord_82497
  simp only [CollatzResearch.WordTrace]
  refine ⟨3008912782134933210997745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2005941854756622140665163 3008912782134933210997745)
  ·
    refine ⟨2256684586601199908248309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3008912782134933210997745 2256684586601199908248309)
    ·
      refine ⟨211564179993862491398279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2256684586601199908248309 211564179993862491398279)
      ·
        refine ⟨317346269990793737097419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211564179993862491398279 317346269990793737097419)
        ·
          refine ⟨476019404986190605646129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317346269990793737097419 476019404986190605646129)
          ·
            refine ⟨357014553739642954234597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 476019404986190605646129 357014553739642954234597)
            ·
              refine ⟨66940228826183053918987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 357014553739642954234597 66940228826183053918987)
              ·
                refine ⟨100410343239274580878481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66940228826183053918987 100410343239274580878481)
                ·
                  refine ⟨75307757429455935658861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100410343239274580878481 75307757429455935658861)
                  ·
                    refine ⟨28240409036045975872073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75307757429455935658861 28240409036045975872073)
                    ·
                      rfl

theorem cell22_82497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_82497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_82497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_82497 prefixEnd_82497 := by exact prefixLift 82497
  have htrace : WordTrace (prefixWord ++ tailWord_82497) baseStart_82497 baseEnd_82497 := by
    simpa [prefixWord, tailWord_82497, baseEnd_82497] using wordTrace_append hprefix tailTrace_82497
  have hstable : (prefixWord ++ tailWord_82497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82497).length < 2 ^ (prefixWord ++ tailWord_82497).sum := by decide
  have hdescent : baseEnd_82497 < baseStart_82497 := by decide
  rcases family_descends (prefixWord ++ tailWord_82497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82508 : List Nat := [2, 2, 1, 3, 1, 2, 2, 1, 5, 3]
def baseStart_82508 : Nat := 118140960795 + 82508 * 2 ^ 59
def prefixEnd_82508 : Nat := 4983230072969 + 3 ^ 40 * 82508 * 2
def baseEnd_82508 : Nat := 28244174560845613847039

theorem tailTrace_82508 : CollatzResearch.WordTrace tailWord_82508 prefixEnd_82508 28244174560845613847039 := by
  unfold tailWord_82508
  simp only [CollatzResearch.WordTrace]
  refine ⟨1504656992547541044824089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2006209323396721393098785 1504656992547541044824089)
  ·
    refine ⟨1128492744410655783618067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1504656992547541044824089 1128492744410655783618067)
    ·
      refine ⟨1692739116615983675427101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1128492744410655783618067 1692739116615983675427101)
      ·
        refine ⟨634777168730993878285163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1692739116615983675427101 634777168730993878285163)
        ·
          refine ⟨952165753096490817427745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 634777168730993878285163 952165753096490817427745)
          ·
            refine ⟨714124314822368113070809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 952165753096490817427745 714124314822368113070809)
            ·
              refine ⟨535593236116776084803107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 714124314822368113070809 535593236116776084803107)
              ·
                refine ⟨803389854175164127204661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 535593236116776084803107 803389854175164127204661)
                ·
                  refine ⟨75317798828921636925437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 803389854175164127204661 75317798828921636925437)
                  ·
                    refine ⟨28244174560845613847039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75317798828921636925437 28244174560845613847039)
                    ·
                      rfl

theorem cell22_82508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 5, 3].length) (baseStart_82508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_82508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_82508 prefixEnd_82508 := by exact prefixLift 82508
  have htrace : WordTrace (prefixWord ++ tailWord_82508) baseStart_82508 baseEnd_82508 := by
    simpa [prefixWord, tailWord_82508, baseEnd_82508] using wordTrace_append hprefix tailTrace_82508
  have hstable : (prefixWord ++ tailWord_82508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82508).length < 2 ^ (prefixWord ++ tailWord_82508).sum := by decide
  have hdescent : baseEnd_82508 < baseStart_82508 := by decide
  rcases family_descends (prefixWord ++ tailWord_82508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82553 : List Nat := [1, 2, 1, 3, 3, 3, 1, 1, 2, 5]
def baseStart_82553 : Nat := 118140960795 + 82553 * 2 ^ 59
def prefixEnd_82553 : Nat := 4983230072969 + 3 ^ 40 * 82553 * 2
def baseEnd_82553 : Nat := 28259578980480496471901

theorem tailTrace_82553 : CollatzResearch.WordTrace tailWord_82553 prefixEnd_82553 28259578980480496471901 := by
  unfold tailWord_82553
  simp only [CollatzResearch.WordTrace]
  refine ⟨3010955269932054775036313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2007303513288036516690875 3010955269932054775036313)
  ·
    refine ⟨2258216452449041081277235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3010955269932054775036313 2258216452449041081277235)
    ·
      refine ⟨3387324678673561621915853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2258216452449041081277235 3387324678673561621915853)
      ·
        refine ⟨1270246754502585608218445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3387324678673561621915853 1270246754502585608218445)
        ·
          refine ⟨476342532938469603081917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1270246754502585608218445 476342532938469603081917)
          ·
            refine ⟨178628449851926101155719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 476342532938469603081917 178628449851926101155719)
            ·
              refine ⟨267942674777889151733579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178628449851926101155719 267942674777889151733579)
              ·
                refine ⟨401914012166833727600369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 267942674777889151733579 401914012166833727600369)
                ·
                  refine ⟨301435509125125295700277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 401914012166833727600369 301435509125125295700277)
                  ·
                    refine ⟨28259578980480496471901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 301435509125125295700277 28259578980480496471901)
                    ·
                      rfl

theorem cell22_82553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 5].length) (baseStart_82553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_82553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_82553 prefixEnd_82553 := by exact prefixLift 82553
  have htrace : WordTrace (prefixWord ++ tailWord_82553) baseStart_82553 baseEnd_82553 := by
    simpa [prefixWord, tailWord_82553, baseEnd_82553] using wordTrace_append hprefix tailTrace_82553
  have hstable : (prefixWord ++ tailWord_82553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82553).length < 2 ^ (prefixWord ++ tailWord_82553).sum := by decide
  have hdescent : baseEnd_82553 < baseStart_82553 := by decide
  rcases family_descends (prefixWord ++ tailWord_82553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82720 : List Nat := [2, 1, 1, 5, 1, 2, 1, 2, 3, 4]
def baseStart_82720 : Nat := 118140960795 + 82720 * 2 ^ 59
def prefixEnd_82720 : Nat := 4983230072969 + 3 ^ 40 * 82720 * 2
def baseEnd_82720 : Nat := 28316746493347727546389

theorem tailTrace_82720 : CollatzResearch.WordTrace tailWord_82720 prefixEnd_82720 28316746493347727546389 := by
  unfold tailWord_82720
  simp only [CollatzResearch.WordTrace]
  refine ⟨1508523130163521148182807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2011364173551361530910409 1508523130163521148182807)
  ·
    refine ⟨2262784695245281722274211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1508523130163521148182807 2262784695245281722274211)
    ·
      refine ⟨3394177042867922583411317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2262784695245281722274211 3394177042867922583411317)
      ·
        refine ⟨318204097768867742194811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3394177042867922583411317 318204097768867742194811)
        ·
          refine ⟨477306146653301613292217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318204097768867742194811 477306146653301613292217)
          ·
            refine ⟨357979609989976209969163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 477306146653301613292217 357979609989976209969163)
            ·
              refine ⟨536969414984964314953745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357979609989976209969163 536969414984964314953745)
              ·
                refine ⟨402727061238723236215309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 536969414984964314953745 402727061238723236215309)
                ·
                  refine ⟨151022647964521213580741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 402727061238723236215309 151022647964521213580741)
                  ·
                    refine ⟨28316746493347727546389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 151022647964521213580741 28316746493347727546389)
                    ·
                      rfl

theorem cell22_82720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 3, 4].length) (baseStart_82720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_82720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_82720 prefixEnd_82720 := by exact prefixLift 82720
  have htrace : WordTrace (prefixWord ++ tailWord_82720) baseStart_82720 baseEnd_82720 := by
    simpa [prefixWord, tailWord_82720, baseEnd_82720] using wordTrace_append hprefix tailTrace_82720
  have hstable : (prefixWord ++ tailWord_82720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82720).length < 2 ^ (prefixWord ++ tailWord_82720).sum := by decide
  have hdescent : baseEnd_82720 < baseStart_82720 := by decide
  rcases family_descends (prefixWord ++ tailWord_82720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82758 : List Nat := [6, 1, 1, 2, 3, 1, 1, 2, 5]
def baseStart_82758 : Nat := 118140960795 + 82758 * 2 ^ 59
def prefixEnd_82758 : Nat := 4983230072969 + 3 ^ 40 * 82758 * 2
def baseEnd_82758 : Nat := 9443251556642765032091

theorem tailTrace_82758 : CollatzResearch.WordTrace tailWord_82758 prefixEnd_82758 9443251556642765032091 := by
  unfold tailWord_82758
  simp only [CollatzResearch.WordTrace]
  refine ⟨94326007318417962070279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2012288156126249857499285 94326007318417962070279)
  ·
    refine ⟨141489010977626943105419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94326007318417962070279 141489010977626943105419)
    ·
      refine ⟨212233516466440414658129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 141489010977626943105419 212233516466440414658129)
      ·
        refine ⟨159175137349830310993597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 212233516466440414658129 159175137349830310993597)
        ·
          refine ⟨59690676506186366622599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159175137349830310993597 59690676506186366622599)
          ·
            refine ⟨89536014759279549933899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59690676506186366622599 89536014759279549933899)
            ·
              refine ⟨134304022138919324900849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89536014759279549933899 134304022138919324900849)
              ·
                refine ⟨100728016604189493675637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134304022138919324900849 100728016604189493675637)
                ·
                  refine ⟨9443251556642765032091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 100728016604189493675637 9443251556642765032091)
                  ·
                    rfl

theorem cell22_82758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_82758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_82758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_82758 prefixEnd_82758 := by exact prefixLift 82758
  have htrace : WordTrace (prefixWord ++ tailWord_82758) baseStart_82758 baseEnd_82758 := by
    simpa [prefixWord, tailWord_82758, baseEnd_82758] using wordTrace_append hprefix tailTrace_82758
  have hstable : (prefixWord ++ tailWord_82758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82758).length < 2 ^ (prefixWord ++ tailWord_82758).sum := by decide
  have hdescent : baseEnd_82758 < baseStart_82758 := by decide
  rcases family_descends (prefixWord ++ tailWord_82758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82784 : List Nat := [2, 1, 1, 3, 3, 1, 5, 1, 2, 3]
def baseStart_82784 : Nat := 118140960795 + 82784 * 2 ^ 59
def prefixEnd_82784 : Nat := 4983230072969 + 3 ^ 40 * 82784 * 2
def baseEnd_82784 : Nat := 28338655001272893946193

theorem tailTrace_82784 : CollatzResearch.WordTrace tailWord_82784 prefixEnd_82784 28338655001272893946193 := by
  unfold tailWord_82784
  simp only [CollatzResearch.WordTrace]
  refine ⟨1509690266047590613347703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2012920354730120817796937 1509690266047590613347703)
  ·
    refine ⟨2264535399071385920021555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1509690266047590613347703 2264535399071385920021555)
    ·
      refine ⟨3396803098607078880032333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2264535399071385920021555 3396803098607078880032333)
      ·
        refine ⟨1273801161977654580012125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3396803098607078880032333 1273801161977654580012125)
        ·
          refine ⟨477675435741620467504547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1273801161977654580012125 477675435741620467504547)
          ·
            refine ⟨716513153612430701256821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 477675435741620467504547 716513153612430701256821)
            ·
              refine ⟨67173108151165378242827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 716513153612430701256821 67173108151165378242827)
              ·
                refine ⟨100759662226748067364241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67173108151165378242827 100759662226748067364241)
                ·
                  refine ⟨75569746670061050523181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100759662226748067364241 75569746670061050523181)
                  ·
                    refine ⟨28338655001272893946193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75569746670061050523181 28338655001272893946193)
                    ·
                      rfl

theorem cell22_82784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 2, 3].length) (baseStart_82784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_82784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_82784 prefixEnd_82784 := by exact prefixLift 82784
  have htrace : WordTrace (prefixWord ++ tailWord_82784) baseStart_82784 baseEnd_82784 := by
    simpa [prefixWord, tailWord_82784, baseEnd_82784] using wordTrace_append hprefix tailTrace_82784
  have hstable : (prefixWord ++ tailWord_82784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82784).length < 2 ^ (prefixWord ++ tailWord_82784).sum := by decide
  have hdescent : baseEnd_82784 < baseStart_82784 := by decide
  rcases family_descends (prefixWord ++ tailWord_82784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82814 : List Nat := [4, 2, 3, 1, 2, 2, 8]
def baseStart_82814 : Nat := 118140960795 + 82814 * 2 ^ 59
def prefixEnd_82814 : Nat := 4983230072969 + 3 ^ 40 * 82814 * 2
def baseEnd_82814 : Nat := 1049960170902326507263

theorem tailTrace_82814 : CollatzResearch.WordTrace tailWord_82814 prefixEnd_82814 1049960170902326507263 := by
  unfold tailWord_82814
  simp only [CollatzResearch.WordTrace]
  refine ⟨377559340248312043785937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2013649814657664233524997 377559340248312043785937)
  ·
    refine ⟨283169505186234032839453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 377559340248312043785937 283169505186234032839453)
    ·
      refine ⟨106188564444837762314795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 283169505186234032839453 106188564444837762314795)
      ·
        refine ⟨159282846667256643472193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106188564444837762314795 159282846667256643472193)
        ·
          refine ⟨119462135000442482604145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159282846667256643472193 119462135000442482604145)
          ·
            refine ⟨89596601250331861953109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119462135000442482604145 89596601250331861953109)
            ·
              refine ⟨1049960170902326507263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 89596601250331861953109 1049960170902326507263)
              ·
                rfl

theorem cell22_82814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 8].length) (baseStart_82814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_82814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_82814 prefixEnd_82814 := by exact prefixLift 82814
  have htrace : WordTrace (prefixWord ++ tailWord_82814) baseStart_82814 baseEnd_82814 := by
    simpa [prefixWord, tailWord_82814, baseEnd_82814] using wordTrace_append hprefix tailTrace_82814
  have hstable : (prefixWord ++ tailWord_82814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82814).length < 2 ^ (prefixWord ++ tailWord_82814).sum := by decide
  have hdescent : baseEnd_82814 < baseStart_82814 := by decide
  rcases family_descends (prefixWord ++ tailWord_82814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82825 : List Nat := [1, 2, 1, 1, 5, 2, 2, 1, 7]
def baseStart_82825 : Nat := 118140960795 + 82825 * 2 ^ 59
def prefixEnd_82825 : Nat := 4983230072969 + 3 ^ 40 * 82825 * 2
def baseEnd_82825 : Nat := 9450896713054151223689

theorem tailTrace_82825 : CollatzResearch.WordTrace tailWord_82825 prefixEnd_82825 9450896713054151223689 := by
  unfold tailWord_82825
  simp only [CollatzResearch.WordTrace]
  refine ⟨3020875924946645228937929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2013917283297763485958619 3020875924946645228937929)
  ·
    refine ⟨2265656943709983921703447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3020875924946645228937929 2265656943709983921703447)
    ·
      refine ⟨3398485415564975882555171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2265656943709983921703447 3398485415564975882555171)
      ·
        refine ⟨5097728123347463823832757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3398485415564975882555171 5097728123347463823832757)
        ·
          refine ⟨477912011563824733484321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5097728123347463823832757 477912011563824733484321)
          ·
            refine ⟨358434008672868550113241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 477912011563824733484321 358434008672868550113241)
            ·
              refine ⟨268825506504651412584931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 358434008672868550113241 268825506504651412584931)
              ·
                refine ⟨403238259756977118877397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 268825506504651412584931 403238259756977118877397)
                ·
                  refine ⟨9450896713054151223689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 403238259756977118877397 9450896713054151223689)
                  ·
                    rfl

theorem cell22_82825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 7].length) (baseStart_82825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_82825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_82825 prefixEnd_82825 := by exact prefixLift 82825
  have htrace : WordTrace (prefixWord ++ tailWord_82825) baseStart_82825 baseEnd_82825 := by
    simpa [prefixWord, tailWord_82825, baseEnd_82825] using wordTrace_append hprefix tailTrace_82825
  have hstable : (prefixWord ++ tailWord_82825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82825).length < 2 ^ (prefixWord ++ tailWord_82825).sum := by decide
  have hdescent : baseEnd_82825 < baseStart_82825 := by decide
  rcases family_descends (prefixWord ++ tailWord_82825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82960 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 11]
def baseStart_82960 : Nat := 118140960795 + 82960 * 2 ^ 59
def prefixEnd_82960 : Nat := 4983230072969 + 3 ^ 40 * 82960 * 2
def baseEnd_82960 : Nat := 9466301132689033848551

theorem tailTrace_82960 : CollatzResearch.WordTrace tailWord_82960 prefixEnd_82960 9466301132689033848551 := by
  unfold tailWord_82960
  simp only [CollatzResearch.WordTrace]
  refine ⟨1512899889728781642551167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2017199852971708856734889 1512899889728781642551167)
  ·
    refine ⟨2269349834593172463826751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1512899889728781642551167 2269349834593172463826751)
    ·
      refine ⟨3404024751889758695740127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2269349834593172463826751 3404024751889758695740127)
      ·
        refine ⟨5106037127834638043610191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3404024751889758695740127 5106037127834638043610191)
        ·
          refine ⟨7659055691751957065415287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5106037127834638043610191 7659055691751957065415287)
          ·
            refine ⟨11488583537627935598122931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7659055691751957065415287 11488583537627935598122931)
            ·
              refine ⟨17232875306441903397184397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11488583537627935598122931 17232875306441903397184397)
              ·
                refine ⟨6462328239915713773944149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17232875306441903397184397 6462328239915713773944149)
                ·
                  refine ⟨9466301132689033848551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 6462328239915713773944149 9466301132689033848551)
                  ·
                    rfl

theorem cell22_82960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 11].length) (baseStart_82960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_82960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_82960 prefixEnd_82960 := by exact prefixLift 82960
  have htrace : WordTrace (prefixWord ++ tailWord_82960) baseStart_82960 baseEnd_82960 := by
    simpa [prefixWord, tailWord_82960, baseEnd_82960] using wordTrace_append hprefix tailTrace_82960
  have hstable : (prefixWord ++ tailWord_82960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82960).length < 2 ^ (prefixWord ++ tailWord_82960).sum := by decide
  have hdescent : baseEnd_82960 < baseStart_82960 := by decide
  rcases family_descends (prefixWord ++ tailWord_82960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82977 : List Nat := [1, 2, 3, 2, 3, 1, 1, 2, 7]
def baseStart_82977 : Nat := 118140960795 + 82977 * 2 ^ 59
def prefixEnd_82977 : Nat := 4983230072969 + 3 ^ 40 * 82977 * 2
def baseEnd_82977 : Nat := 9468240948494907956867

theorem tailTrace_82977 : CollatzResearch.WordTrace tailWord_82977 prefixEnd_82977 9468240948494907956867 := by
  unfold tailWord_82977
  simp only [CollatzResearch.WordTrace]
  refine ⟨3026419820395975188471185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2017613213597316792314123 3026419820395975188471185)
  ·
    refine ⟨2269814865296981391353389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3026419820395975188471185 2269814865296981391353389)
    ·
      refine ⟨851180574486368021757521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2269814865296981391353389 851180574486368021757521)
      ·
        refine ⟨638385430864776016318141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 851180574486368021757521 638385430864776016318141)
        ·
          refine ⟨239394536574291006119303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 638385430864776016318141 239394536574291006119303)
          ·
            refine ⟨359091804861436509178955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239394536574291006119303 359091804861436509178955)
            ·
              refine ⟨538637707292154763768433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 359091804861436509178955 538637707292154763768433)
              ·
                refine ⟨403978280469116072826325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 538637707292154763768433 403978280469116072826325)
                ·
                  refine ⟨9468240948494907956867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 403978280469116072826325 9468240948494907956867)
                  ·
                    rfl

theorem cell22_82977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 7].length) (baseStart_82977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_82977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_82977 prefixEnd_82977 := by exact prefixLift 82977
  have htrace : WordTrace (prefixWord ++ tailWord_82977) baseStart_82977 baseEnd_82977 := by
    simpa [prefixWord, tailWord_82977, baseEnd_82977] using wordTrace_append hprefix tailTrace_82977
  have hstable : (prefixWord ++ tailWord_82977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82977).length < 2 ^ (prefixWord ++ tailWord_82977).sum := by decide
  have hdescent : baseEnd_82977 < baseStart_82977 := by decide
  rcases family_descends (prefixWord ++ tailWord_82977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82998 : List Nat := [5, 1, 2, 1, 1, 4, 1, 1, 3, 3]
def baseStart_82998 : Nat := 118140960795 + 82998 * 2 ^ 59
def prefixEnd_82998 : Nat := 4983230072969 + 3 ^ 40 * 82998 * 2
def baseEnd_82998 : Nat := 28411911574647669095537

theorem tailTrace_82998 : CollatzResearch.WordTrace tailWord_82998 prefixEnd_82998 28411911574647669095537 := by
  unfold tailWord_82998
  simp only [CollatzResearch.WordTrace]
  refine ⟨189199109582493485936603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2018123835546597183323765 189199109582493485936603)
  ·
    refine ⟨283798664373740228904905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 189199109582493485936603 283798664373740228904905)
    ·
      refine ⟨212848998280305171678679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 283798664373740228904905 212848998280305171678679)
      ·
        refine ⟨319273497420457757518019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212848998280305171678679 319273497420457757518019)
        ·
          refine ⟨478910246130686636277029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319273497420457757518019 478910246130686636277029)
          ·
            refine ⟨89795671149503744301943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 478910246130686636277029 89795671149503744301943)
            ·
              refine ⟨134693506724255616452915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89795671149503744301943 134693506724255616452915)
              ·
                refine ⟨202040260086383424679373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134693506724255616452915 202040260086383424679373)
                ·
                  refine ⟨75765097532393784254765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 202040260086383424679373 75765097532393784254765)
                  ·
                    refine ⟨28411911574647669095537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75765097532393784254765 28411911574647669095537)
                    ·
                      rfl

theorem cell22_82998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_82998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_82998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_82998 prefixEnd_82998 := by exact prefixLift 82998
  have htrace : WordTrace (prefixWord ++ tailWord_82998) baseStart_82998 baseEnd_82998 := by
    simpa [prefixWord, tailWord_82998, baseEnd_82998] using wordTrace_append hprefix tailTrace_82998
  have hstable : (prefixWord ++ tailWord_82998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82998).length < 2 ^ (prefixWord ++ tailWord_82998).sum := by decide
  have hdescent : baseEnd_82998 < baseStart_82998 := by decide
  rcases family_descends (prefixWord ++ tailWord_82998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83007 : List Nat := [1, 1, 2, 2, 3, 1, 1, 4, 3, 4]
def baseStart_83007 : Nat := 118140960795 + 83007 * 2 ^ 59
def prefixEnd_83007 : Nat := 4983230072969 + 3 ^ 40 * 83007 * 2
def baseEnd_83007 : Nat := 28414992458574645620509

theorem tailTrace_83007 : CollatzResearch.WordTrace tailWord_83007 prefixEnd_83007 28414992458574645620509 := by
  unfold tailWord_83007
  simp only [CollatzResearch.WordTrace]
  refine ⟨3027514010287290312063275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2018342673524860208042183 3027514010287290312063275)
  ·
    refine ⟨4541271015430935468094913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3027514010287290312063275 4541271015430935468094913)
    ·
      refine ⟨3405953261573201601071185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4541271015430935468094913 3405953261573201601071185)
      ·
        refine ⟨2554464946179901200803389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3405953261573201601071185 2554464946179901200803389)
        ·
          refine ⟨957924354817462950301271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2554464946179901200803389 957924354817462950301271)
          ·
            refine ⟨1436886532226194425451907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 957924354817462950301271 1436886532226194425451907)
            ·
              refine ⟨2155329798339291638177861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1436886532226194425451907 2155329798339291638177861)
              ·
                refine ⟨404124337188617182158349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2155329798339291638177861 404124337188617182158349)
                ·
                  refine ⟨151546626445731443309381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 404124337188617182158349 151546626445731443309381)
                  ·
                    refine ⟨28414992458574645620509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 151546626445731443309381 28414992458574645620509)
                    ·
                      rfl

theorem cell22_83007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 4].length) (baseStart_83007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_83007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_83007 prefixEnd_83007 := by exact prefixLift 83007
  have htrace : WordTrace (prefixWord ++ tailWord_83007) baseStart_83007 baseEnd_83007 := by
    simpa [prefixWord, tailWord_83007, baseEnd_83007] using wordTrace_append hprefix tailTrace_83007
  have hstable : (prefixWord ++ tailWord_83007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83007).length < 2 ^ (prefixWord ++ tailWord_83007).sum := by decide
  have hdescent : baseEnd_83007 < baseStart_83007 := by decide
  rcases family_descends (prefixWord ++ tailWord_83007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83022 : List Nat := [4, 1, 1, 1, 1, 3, 2, 1, 8]
def baseStart_83022 : Nat := 118140960795 + 83022 * 2 ^ 59
def prefixEnd_83022 : Nat := 4983230072969 + 3 ^ 40 * 83022 * 2
def baseEnd_83022 : Nat := 9473375755039868831821

theorem tailTrace_83022 : CollatzResearch.WordTrace tailWord_83022 prefixEnd_83022 9473375755039868831821 := by
  unfold tailWord_83022
  simp only [CollatzResearch.WordTrace]
  refine ⟨378507638154118484232415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2018707403488631915906213 378507638154118484232415)
  ·
    refine ⟨567761457231177726348623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 378507638154118484232415 567761457231177726348623)
    ·
      refine ⟨851642185846766589522935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 567761457231177726348623 851642185846766589522935)
      ·
        refine ⟨1277463278770149884284403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 851642185846766589522935 1277463278770149884284403)
        ·
          refine ⟨1916194918155224826426605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1277463278770149884284403 1916194918155224826426605)
          ·
            refine ⟨718573094308209309909977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1916194918155224826426605 718573094308209309909977)
            ·
              refine ⟨538929820731156982432483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 718573094308209309909977 538929820731156982432483)
              ·
                refine ⟨808394731096735473648725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 538929820731156982432483 808394731096735473648725)
                ·
                  refine ⟨9473375755039868831821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 808394731096735473648725 9473375755039868831821)
                  ·
                    rfl

theorem cell22_83022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 8].length) (baseStart_83022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_83022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_83022 prefixEnd_83022 := by exact prefixLift 83022
  have htrace : WordTrace (prefixWord ++ tailWord_83022) baseStart_83022 baseEnd_83022 := by
    simpa [prefixWord, tailWord_83022, baseEnd_83022] using wordTrace_append hprefix tailTrace_83022
  have hstable : (prefixWord ++ tailWord_83022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83022).length < 2 ^ (prefixWord ++ tailWord_83022).sum := by decide
  have hdescent : baseEnd_83022 < baseStart_83022 := by decide
  rcases family_descends (prefixWord ++ tailWord_83022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83039 : List Nat := [1, 1, 2, 3, 1, 1, 4, 5, 4]
def baseStart_83039 : Nat := 118140960795 + 83039 * 2 ^ 59
def prefixEnd_83039 : Nat := 4983230072969 + 3 ^ 40 * 83039 * 2
def baseEnd_83039 : Nat := 9475315570845742940137

theorem tailTrace_83039 : CollatzResearch.WordTrace tailWord_83039 prefixEnd_83039 9475315570845742940137 := by
  unfold tailWord_83039
  simp only [CollatzResearch.WordTrace]
  refine ⟨3028681146171359777228171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2019120764114239851485447 3028681146171359777228171)
  ·
    refine ⟨4543021719257039665842257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3028681146171359777228171 4543021719257039665842257)
    ·
      refine ⟨3407266289442779749381693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4543021719257039665842257 3407266289442779749381693)
      ·
        refine ⟨1277724858541042406018135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3407266289442779749381693 1277724858541042406018135)
        ·
          refine ⟨1916587287811563609027203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1277724858541042406018135 1916587287811563609027203)
          ·
            refine ⟨2874880931717345413540805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1916587287811563609027203 2874880931717345413540805)
            ·
              refine ⟨539040174697002265038901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2874880931717345413540805 539040174697002265038901)
              ·
                refine ⟨50535016377843962347397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 539040174697002265038901 50535016377843962347397)
                ·
                  refine ⟨9475315570845742940137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50535016377843962347397 9475315570845742940137)
                  ·
                    rfl

theorem cell22_83039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 5, 4].length) (baseStart_83039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_83039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_83039 prefixEnd_83039 := by exact prefixLift 83039
  have htrace : WordTrace (prefixWord ++ tailWord_83039) baseStart_83039 baseEnd_83039 := by
    simpa [prefixWord, tailWord_83039, baseEnd_83039] using wordTrace_append hprefix tailTrace_83039
  have hstable : (prefixWord ++ tailWord_83039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83039).length < 2 ^ (prefixWord ++ tailWord_83039).sum := by decide
  have hdescent : baseEnd_83039 < baseStart_83039 := by decide
  rcases family_descends (prefixWord ++ tailWord_83039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83086 : List Nat := [4, 1, 1, 3, 2, 1, 3, 1, 2, 4]
def baseStart_83086 : Nat := 118140960795 + 83086 * 2 ^ 59
def prefixEnd_83086 : Nat := 4983230072969 + 3 ^ 40 * 83086 * 2
def baseEnd_83086 : Nat := 28442035773044772895267

theorem tailTrace_83086 : CollatzResearch.WordTrace tailWord_83086 prefixEnd_83086 28442035773044772895267 := by
  unfold tailWord_83086
  simp only [CollatzResearch.WordTrace]
  refine ⟨378799422125135850523639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2020263584667391202792741 378799422125135850523639)
  ·
    refine ⟨568199133187703775785459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 378799422125135850523639 568199133187703775785459)
    ·
      refine ⟨852298699781555663678189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 568199133187703775785459 852298699781555663678189)
      ·
        refine ⟨319612012418083373879321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 852298699781555663678189 319612012418083373879321)
        ·
          refine ⟨239709009313562530409491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 319612012418083373879321 239709009313562530409491)
          ·
            refine ⟨359563513970343795614237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239709009313562530409491 359563513970343795614237)
            ·
              refine ⟨134836317738878923355339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 359563513970343795614237 134836317738878923355339)
              ·
                refine ⟨202254476608318385033009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134836317738878923355339 202254476608318385033009)
                ·
                  refine ⟨151690857456238788774757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 202254476608318385033009 151690857456238788774757)
                  ·
                    refine ⟨28442035773044772895267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 151690857456238788774757 28442035773044772895267)
                    ·
                      rfl

theorem cell22_83086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_83086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_83086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_83086 prefixEnd_83086 := by exact prefixLift 83086
  have htrace : WordTrace (prefixWord ++ tailWord_83086) baseStart_83086 baseEnd_83086 := by
    simpa [prefixWord, tailWord_83086, baseEnd_83086] using wordTrace_append hprefix tailTrace_83086
  have hstable : (prefixWord ++ tailWord_83086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83086).length < 2 ^ (prefixWord ++ tailWord_83086).sum := by decide
  have hdescent : baseEnd_83086 < baseStart_83086 := by decide
  rcases family_descends (prefixWord ++ tailWord_83086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83223 : List Nat := [1, 1, 3, 4, 1, 1, 4, 2, 2, 3]
def baseStart_83223 : Nat := 118140960795 + 83223 * 2 ^ 59
def prefixEnd_83223 : Nat := 4983230072969 + 3 ^ 40 * 83223 * 2
def baseEnd_83223 : Nat := 28488933672822082219847

theorem tailTrace_83223 : CollatzResearch.WordTrace tailWord_83223 prefixEnd_83223 28488933672822082219847 := by
  unfold tailWord_83223
  simp only [CollatzResearch.WordTrace]
  refine ⟨3035392177504759201926323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2023594785003172801284215 3035392177504759201926323)
  ·
    refine ⟨4553088266257138802889485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3035392177504759201926323 4553088266257138802889485)
    ·
      refine ⟨1707408099846427051083557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4553088266257138802889485 1707408099846427051083557)
      ·
        refine ⟨320139018721205072078167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1707408099846427051083557 320139018721205072078167)
        ·
          refine ⟨480208528081807608117251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320139018721205072078167 480208528081807608117251)
          ·
            refine ⟨720312792122711412175877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 480208528081807608117251 720312792122711412175877)
            ·
              refine ⟨135058648523008389782977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 720312792122711412175877 135058648523008389782977)
              ·
                refine ⟨101293986392256292337233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135058648523008389782977 101293986392256292337233)
                ·
                  refine ⟨75970489794192219252925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101293986392256292337233 75970489794192219252925)
                  ·
                    refine ⟨28488933672822082219847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75970489794192219252925 28488933672822082219847)
                    ·
                      rfl

theorem cell22_83223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 2, 3].length) (baseStart_83223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_83223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_83223 prefixEnd_83223 := by exact prefixLift 83223
  have htrace : WordTrace (prefixWord ++ tailWord_83223) baseStart_83223 baseEnd_83223 := by
    simpa [prefixWord, tailWord_83223, baseEnd_83223] using wordTrace_append hprefix tailTrace_83223
  have hstable : (prefixWord ++ tailWord_83223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83223).length < 2 ^ (prefixWord ++ tailWord_83223).sum := by decide
  have hdescent : baseEnd_83223 < baseStart_83223 := by decide
  rcases family_descends (prefixWord ++ tailWord_83223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83251 : List Nat := [1, 1, 1, 2, 5, 2, 1, 1, 5, 3]
def baseStart_83251 : Nat := 118140960795 + 83251 * 2 ^ 59
def prefixEnd_83251 : Nat := 4983230072969 + 3 ^ 40 * 83251 * 2
def baseEnd_83251 : Nat := 28498518645039342519761

theorem tailTrace_83251 : CollatzResearch.WordTrace tailWord_83251 prefixEnd_83251 28498518645039342519761 := by
  unfold tailWord_83251
  simp only [CollatzResearch.WordTrace]
  refine ⟨3036413421403319983945607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2024275614268879989297071 3036413421403319983945607)
  ·
    refine ⟨4554620132104979975918411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3036413421403319983945607 4554620132104979975918411)
    ·
      refine ⟨6831930198157469963877617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4554620132104979975918411 6831930198157469963877617)
      ·
        refine ⟨5123947648618102472908213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6831930198157469963877617 5123947648618102472908213)
        ·
          refine ⟨480370092057947106835145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5123947648618102472908213 480370092057947106835145)
          ·
            refine ⟨360277569043460330126359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 480370092057947106835145 360277569043460330126359)
            ·
              refine ⟨540416353565190495189539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360277569043460330126359 540416353565190495189539)
              ·
                refine ⟨810624530347785742784309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 540416353565190495189539 810624530347785742784309)
                ·
                  refine ⟨75996049720104913386029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 810624530347785742784309 75996049720104913386029)
                  ·
                    refine ⟨28498518645039342519761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 75996049720104913386029 28498518645039342519761)
                    ·
                      rfl

theorem cell22_83251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 5, 3].length) (baseStart_83251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_83251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_83251 prefixEnd_83251 := by exact prefixLift 83251
  have htrace : WordTrace (prefixWord ++ tailWord_83251) baseStart_83251 baseEnd_83251 := by
    simpa [prefixWord, tailWord_83251, baseEnd_83251] using wordTrace_append hprefix tailTrace_83251
  have hstable : (prefixWord ++ tailWord_83251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83251).length < 2 ^ (prefixWord ++ tailWord_83251).sum := by decide
  have hdescent : baseEnd_83251 < baseStart_83251 := by decide
  rcases family_descends (prefixWord ++ tailWord_83251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83264 : List Nat := [2, 1, 1, 2, 2, 1, 4, 2, 7]
def baseStart_83264 : Nat := 118140960795 + 83264 * 2 ^ 59
def prefixEnd_83264 : Nat := 4983230072969 + 3 ^ 40 * 83264 * 2
def baseEnd_83264 : Nat := 9500989603570547314907

theorem tailTrace_83264 : CollatzResearch.WordTrace tailWord_83264 prefixEnd_83264 9500989603570547314907 := by
  unfold tailWord_83264
  simp only [CollatzResearch.WordTrace]
  refine ⟨1518443785178111602084423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2024591713570815469445897 1518443785178111602084423)
  ·
    refine ⟨2277665677767167403126635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1518443785178111602084423 2277665677767167403126635)
    ·
      refine ⟨3416498516650751104689953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2277665677767167403126635 3416498516650751104689953)
      ·
        refine ⟨2562373887488063328517465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3416498516650751104689953 2562373887488063328517465)
        ·
          refine ⟨1921780415616047496388099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2562373887488063328517465 1921780415616047496388099)
          ·
            refine ⟨2882670623424071244582149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1921780415616047496388099 2882670623424071244582149)
            ·
              refine ⟨540500741892013358359153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2882670623424071244582149 540500741892013358359153)
              ·
                refine ⟨405375556419010018769365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 540500741892013358359153 405375556419010018769365)
                ·
                  refine ⟨9500989603570547314907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 405375556419010018769365 9500989603570547314907)
                  ·
                    rfl

theorem cell22_83264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 7].length) (baseStart_83264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_83264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_83264 prefixEnd_83264 := by exact prefixLift 83264
  have htrace : WordTrace (prefixWord ++ tailWord_83264) baseStart_83264 baseEnd_83264 := by
    simpa [prefixWord, tailWord_83264, baseEnd_83264] using wordTrace_append hprefix tailTrace_83264
  have hstable : (prefixWord ++ tailWord_83264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83264).length < 2 ^ (prefixWord ++ tailWord_83264).sum := by decide
  have hdescent : baseEnd_83264 < baseStart_83264 := by decide
  rcases family_descends (prefixWord ++ tailWord_83264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83270 : List Nat := [6, 1, 1, 3, 1, 1, 9]
def baseStart_83270 : Nat := 118140960795 + 83270 * 2 ^ 59
def prefixEnd_83270 : Nat := 4983230072969 + 3 ^ 40 * 83270 * 2
def baseEnd_83270 : Nat := 1055741582715912084989

theorem tailTrace_83270 : CollatzResearch.WordTrace tailWord_83270 prefixEnd_83270 1055741582715912084989 := by
  unfold tailWord_83270
  simp only [CollatzResearch.WordTrace]
  refine ⟨94909575260452694652727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2024737605556324152591509 94909575260452694652727)
  ·
    refine ⟨142364362890679041979091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 94909575260452694652727 142364362890679041979091)
    ·
      refine ⟨213546544336018562968637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 142364362890679041979091 213546544336018562968637)
      ·
        refine ⟨80079954126006961113239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213546544336018562968637 80079954126006961113239)
        ·
          refine ⟨120119931189010441669859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80079954126006961113239 120119931189010441669859)
          ·
            refine ⟨180179896783515662504789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120119931189010441669859 180179896783515662504789)
            ·
              refine ⟨1055741582715912084989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 180179896783515662504789 1055741582715912084989)
              ·
                rfl

theorem cell22_83270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 9].length) (baseStart_83270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_83270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_83270 prefixEnd_83270 := by exact prefixLift 83270
  have htrace : WordTrace (prefixWord ++ tailWord_83270) baseStart_83270 baseEnd_83270 := by
    simpa [prefixWord, tailWord_83270, baseEnd_83270] using wordTrace_append hprefix tailTrace_83270
  have hstable : (prefixWord ++ tailWord_83270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83270).length < 2 ^ (prefixWord ++ tailWord_83270).sum := by decide
  have hdescent : baseEnd_83270 < baseStart_83270 := by decide
  rcases family_descends (prefixWord ++ tailWord_83270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83285 : List Nat := [1, 3, 2, 2, 3, 1, 2, 4, 1, 3]
def baseStart_83285 : Nat := 118140960795 + 83285 * 2 ^ 59
def prefixEnd_83285 : Nat := 4983230072969 + 3 ^ 40 * 83285 * 2
def baseEnd_83285 : Nat := 28510157539874587169657

theorem tailTrace_83285 : CollatzResearch.WordTrace tailWord_83285 prefixEnd_83285 28510157539874587169657 := by
  unfold tailWord_83285
  simp only [CollatzResearch.WordTrace]
  refine ⟨3037653503280143790683309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2025102335520095860455539 3037653503280143790683309)
  ·
    refine ⟨1139120063730053921506241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3037653503280143790683309 1139120063730053921506241)
    ·
      refine ⟨854340047797540441129681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1139120063730053921506241 854340047797540441129681)
      ·
        refine ⟨640755035848155330847261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 854340047797540441129681 640755035848155330847261)
        ·
          refine ⟨240283138443058249067723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 640755035848155330847261 240283138443058249067723)
          ·
            refine ⟨360424707664587373601585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240283138443058249067723 360424707664587373601585)
            ·
              refine ⟨270318530748440530201189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 360424707664587373601585 270318530748440530201189)
              ·
                refine ⟨50684724515332599412723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 270318530748440530201189 50684724515332599412723)
                ·
                  refine ⟨76027086772998899119085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 50684724515332599412723 76027086772998899119085)
                  ·
                    refine ⟨28510157539874587169657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 76027086772998899119085 28510157539874587169657)
                    ·
                      rfl

theorem cell22_83285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 4, 1, 3].length) (baseStart_83285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_83285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_83285 prefixEnd_83285 := by exact prefixLift 83285
  have htrace : WordTrace (prefixWord ++ tailWord_83285) baseStart_83285 baseEnd_83285 := by
    simpa [prefixWord, tailWord_83285, baseEnd_83285] using wordTrace_append hprefix tailTrace_83285
  have hstable : (prefixWord ++ tailWord_83285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83285).length < 2 ^ (prefixWord ++ tailWord_83285).sum := by decide
  have hdescent : baseEnd_83285 < baseStart_83285 := by decide
  rcases family_descends (prefixWord ++ tailWord_83285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83296 : List Nat := [2, 1, 1, 3, 4, 1, 2, 1, 2, 5]
def baseStart_83296 : Nat := 118140960795 + 83296 * 2 ^ 59
def prefixEnd_83296 : Nat := 4983230072969 + 3 ^ 40 * 83296 * 2
def baseEnd_83296 : Nat := 28513923064674225144623

theorem tailTrace_83296 : CollatzResearch.WordTrace tailWord_83296 prefixEnd_83296 28513923064674225144623 := by
  unfold tailWord_83296
  simp only [CollatzResearch.WordTrace]
  refine ⟨1519027353120146334666871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2025369804160195112889161 1519027353120146334666871)
  ·
    refine ⟨2278541029680219502000307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1519027353120146334666871 2278541029680219502000307)
    ·
      refine ⟨3417811544520329253000461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2278541029680219502000307 3417811544520329253000461)
      ·
        refine ⟨1281679329195123469875173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3417811544520329253000461 1281679329195123469875173)
        ·
          refine ⟨240314874224085650601595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1281679329195123469875173 240314874224085650601595)
          ·
            refine ⟨360472311336128475902393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240314874224085650601595 360472311336128475902393)
            ·
              refine ⟨270354233502096356926795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 360472311336128475902393 270354233502096356926795)
              ·
                refine ⟨405531350253144535390193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270354233502096356926795 405531350253144535390193)
                ·
                  refine ⟨304148512689858401542645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 405531350253144535390193 304148512689858401542645)
                  ·
                    refine ⟨28513923064674225144623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 304148512689858401542645 28513923064674225144623)
                    ·
                      rfl

theorem cell22_83296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 2, 5].length) (baseStart_83296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_83296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_83296 prefixEnd_83296 := by exact prefixLift 83296
  have htrace : WordTrace (prefixWord ++ tailWord_83296) baseStart_83296 baseEnd_83296 := by
    simpa [prefixWord, tailWord_83296, baseEnd_83296] using wordTrace_append hprefix tailTrace_83296
  have hstable : (prefixWord ++ tailWord_83296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83296).length < 2 ^ (prefixWord ++ tailWord_83296).sum := by decide
  have hdescent : baseEnd_83296 < baseStart_83296 := by decide
  rcases family_descends (prefixWord ++ tailWord_83296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83388 : List Nat := [2, 2, 2, 4, 3, 9]
def baseStart_83388 : Nat := 118140960795 + 83388 * 2 ^ 59
def prefixEnd_83388 : Nat := 4983230072969 + 3 ^ 40 * 83388 * 2
def baseEnd_83388 : Nat := 352412549936008047461

theorem tailTrace_83388 : CollatzResearch.WordTrace tailWord_83388 prefixEnd_83388 352412549936008047461 := by
  unfold tailWord_83388
  simp only [CollatzResearch.WordTrace]
  refine ⟨1520705110953496190841409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2027606814604661587788545 1520705110953496190841409)
  ·
    refine ⟨1140528833215122143131057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1520705110953496190841409 1140528833215122143131057)
    ·
      refine ⟨855396624911341607348293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1140528833215122143131057 855396624911341607348293)
      ·
        refine ⟨160386867170876551377805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 855396624911341607348293 160386867170876551377805)
        ·
          refine ⟨60145075189078706766677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160386867170876551377805 60145075189078706766677)
          ·
            refine ⟨352412549936008047461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 60145075189078706766677 352412549936008047461)
            ·
              rfl

theorem cell22_83388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 9].length) (baseStart_83388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_83388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_83388 prefixEnd_83388 := by exact prefixLift 83388
  have htrace : WordTrace (prefixWord ++ tailWord_83388) baseStart_83388 baseEnd_83388 := by
    simpa [prefixWord, tailWord_83388, baseEnd_83388] using wordTrace_append hprefix tailTrace_83388
  have hstable : (prefixWord ++ tailWord_83388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83388).length < 2 ^ (prefixWord ++ tailWord_83388).sum := by decide
  have hdescent : baseEnd_83388 < baseStart_83388 := by decide
  rcases family_descends (prefixWord ++ tailWord_83388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83454 : List Nat := [4, 2, 2, 3, 1, 1, 2, 1, 3, 3]
def baseStart_83454 : Nat := 118140960795 + 83454 * 2 ^ 59
def prefixEnd_83454 : Nat := 4983230072969 + 3 ^ 40 * 83454 * 2
def baseEnd_83454 : Nat := 28568009693614479694139

theorem tailTrace_83454 : CollatzResearch.WordTrace tailWord_83454 prefixEnd_83454 28568009693614479694139 := by
  unfold tailWord_83454
  simp only [CollatzResearch.WordTrace]
  refine ⟨380477179958485706698177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2029211626445257102390277 380477179958485706698177)
  ·
    refine ⟨285357884968864280023633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 380477179958485706698177 285357884968864280023633)
    ·
      refine ⟨214018413726648210017725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285357884968864280023633 214018413726648210017725)
      ·
        refine ⟨80256905147493078756647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 214018413726648210017725 80256905147493078756647)
        ·
          refine ⟨120385357721239618134971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80256905147493078756647 120385357721239618134971)
          ·
            refine ⟨180578036581859427202457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120385357721239618134971 180578036581859427202457)
            ·
              refine ⟨135433527436394570401843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180578036581859427202457 135433527436394570401843)
              ·
                refine ⟨203150291154591855602765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135433527436394570401843 203150291154591855602765)
                ·
                  refine ⟨76181359182971945851037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 203150291154591855602765 76181359182971945851037)
                  ·
                    refine ⟨28568009693614479694139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 76181359182971945851037 28568009693614479694139)
                    ·
                      rfl

theorem cell22_83454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_83454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_83454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_83454 prefixEnd_83454 := by exact prefixLift 83454
  have htrace : WordTrace (prefixWord ++ tailWord_83454) baseStart_83454 baseEnd_83454 := by
    simpa [prefixWord, tailWord_83454, baseEnd_83454] using wordTrace_append hprefix tailTrace_83454
  have hstable : (prefixWord ++ tailWord_83454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83454).length < 2 ^ (prefixWord ++ tailWord_83454).sum := by decide
  have hdescent : baseEnd_83454 < baseStart_83454 := by decide
  rcases family_descends (prefixWord ++ tailWord_83454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83512 : List Nat := [2, 1, 2, 1, 4, 3, 3, 2, 4]
def baseStart_83512 : Nat := 118140960795 + 83512 * 2 ^ 59
def prefixEnd_83512 : Nat := 4983230072969 + 3 ^ 40 * 83512 * 2
def baseEnd_83512 : Nat := 9529288092973887247987

theorem tailTrace_83512 : CollatzResearch.WordTrace tailWord_83512 prefixEnd_83512 9529288092973887247987 := by
  unfold tailWord_83512
  simp only [CollatzResearch.WordTrace]
  refine ⟨1522966436728880779598395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2030621915638507706131193 1522966436728880779598395)
  ·
    refine ⟨2284449655093321169397593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1522966436728880779598395 2284449655093321169397593)
    ·
      refine ⟨1713337241319990877048195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2284449655093321169397593 1713337241319990877048195)
      ·
        refine ⟨2570005861979986315572293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1713337241319990877048195 2570005861979986315572293)
        ·
          refine ⟨481876099121247434169805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2570005861979986315572293 481876099121247434169805)
          ·
            refine ⟨180703537170467787813677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 481876099121247434169805 180703537170467787813677)
            ·
              refine ⟨67763826438925420430129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 180703537170467787813677 67763826438925420430129)
              ·
                refine ⟨50822869829194065322597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67763826438925420430129 50822869829194065322597)
                ·
                  refine ⟨9529288092973887247987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50822869829194065322597 9529288092973887247987)
                  ·
                    rfl

theorem cell22_83512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 2, 4].length) (baseStart_83512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_83512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_83512 prefixEnd_83512 := by exact prefixLift 83512
  have htrace : WordTrace (prefixWord ++ tailWord_83512) baseStart_83512 baseEnd_83512 := by
    simpa [prefixWord, tailWord_83512, baseEnd_83512] using wordTrace_append hprefix tailTrace_83512
  have hstable : (prefixWord ++ tailWord_83512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83512).length < 2 ^ (prefixWord ++ tailWord_83512).sum := by decide
  have hdescent : baseEnd_83512 < baseStart_83512 := by decide
  rcases family_descends (prefixWord ++ tailWord_83512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83527 : List Nat := [1, 1, 4, 1, 5, 1, 1, 3, 2, 3]
def baseStart_83527 : Nat := 118140960795 + 83527 * 2 ^ 59
def prefixEnd_83527 : Nat := 4983230072969 + 3 ^ 40 * 83527 * 2
def baseEnd_83527 : Nat := 28592999085466622618915

theorem tailTrace_83527 : CollatzResearch.WordTrace tailWord_83527 prefixEnd_83527 28592999085466622618915 := by
  unfold tailWord_83527
  simp only [CollatzResearch.WordTrace]
  refine ⟨3046479968403419120992835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2030986645602279413995223 3046479968403419120992835)
  ·
    refine ⟨4569719952605128681489253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3046479968403419120992835 4569719952605128681489253)
    ·
      refine ⟨856822491113461627779235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4569719952605128681489253 856822491113461627779235)
      ·
        refine ⟨1285233736670192441668853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 856822491113461627779235 1285233736670192441668853)
        ·
          refine ⟨120490662812830541406455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1285233736670192441668853 120490662812830541406455)
          ·
            refine ⟨180735994219245812109683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120490662812830541406455 180735994219245812109683)
            ·
              refine ⟨271103991328868718164525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180735994219245812109683 271103991328868718164525)
              ·
                refine ⟨101663996748325769311697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 271103991328868718164525 101663996748325769311697)
                ·
                  refine ⟨76247997561244326983773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101663996748325769311697 76247997561244326983773)
                  ·
                    refine ⟨28592999085466622618915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 76247997561244326983773 28592999085466622618915)
                    ·
                      rfl

theorem cell22_83527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 2, 3].length) (baseStart_83527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_83527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_83527 prefixEnd_83527 := by exact prefixLift 83527
  have htrace : WordTrace (prefixWord ++ tailWord_83527) baseStart_83527 baseEnd_83527 := by
    simpa [prefixWord, tailWord_83527, baseEnd_83527] using wordTrace_append hprefix tailTrace_83527
  have hstable : (prefixWord ++ tailWord_83527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83527).length < 2 ^ (prefixWord ++ tailWord_83527).sum := by decide
  have hdescent : baseEnd_83527 < baseStart_83527 := by decide
  rcases family_descends (prefixWord ++ tailWord_83527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83585 : List Nat := [1, 2, 4, 2, 1, 2, 2, 3, 5]
def baseStart_83585 : Nat := 118140960795 + 83585 * 2 ^ 59
def prefixEnd_83585 : Nat := 4983230072969 + 3 ^ 40 * 83585 * 2
def baseEnd_83585 : Nat := 9537617890257934889579

theorem tailTrace_83585 : CollatzResearch.WordTrace tailWord_83585 prefixEnd_83585 9537617890257934889579 := by
  unfold tailWord_83585
  simp only [CollatzResearch.WordTrace]
  refine ⟨3048595402193295026604209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2032396934795530017736139 3048595402193295026604209)
  ·
    refine ⟨2286446551644971269953157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3048595402193295026604209 2286446551644971269953157)
    ·
      refine ⟨428708728433432113116217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2286446551644971269953157 428708728433432113116217)
      ·
        refine ⟨321531546325074084837163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 428708728433432113116217 321531546325074084837163)
        ·
          refine ⟨482297319487611127255745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321531546325074084837163 482297319487611127255745)
          ·
            refine ⟨361722989615708345441809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 482297319487611127255745 361722989615708345441809)
            ·
              refine ⟨271292242211781259081357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 361722989615708345441809 271292242211781259081357)
              ·
                refine ⟨101734590829417972155509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 271292242211781259081357 101734590829417972155509)
                ·
                  refine ⟨9537617890257934889579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 101734590829417972155509 9537617890257934889579)
                  ·
                    rfl

theorem cell22_83585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 5].length) (baseStart_83585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_83585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_83585 prefixEnd_83585 := by exact prefixLift 83585
  have htrace : WordTrace (prefixWord ++ tailWord_83585) baseStart_83585 baseEnd_83585 := by
    simpa [prefixWord, tailWord_83585, baseEnd_83585] using wordTrace_append hprefix tailTrace_83585
  have hstable : (prefixWord ++ tailWord_83585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83585).length < 2 ^ (prefixWord ++ tailWord_83585).sum := by decide
  have hdescent : baseEnd_83585 < baseStart_83585 := by decide
  rcases family_descends (prefixWord ++ tailWord_83585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83613 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 10]
def baseStart_83613 : Nat := 118140960795 + 83613 * 2 ^ 59
def prefixEnd_83613 : Nat := 4983230072969 + 3 ^ 40 * 83613 * 2
def baseEnd_83613 : Nat := 9540812880997021656217

theorem tailTrace_83613 : CollatzResearch.WordTrace tailWord_83613 prefixEnd_83613 9540812880997021656217 := by
  unfold tailWord_83613
  simp only [CollatzResearch.WordTrace]
  refine ⟨3049616646091855808623493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2033077764061237205748995 3049616646091855808623493)
  ·
    refine ⟨571803121142222964116905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3049616646091855808623493 571803121142222964116905)
    ·
      refine ⟨428852340856667223087679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 571803121142222964116905 428852340856667223087679)
      ·
        refine ⟨643278511285000834631519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 428852340856667223087679 643278511285000834631519)
        ·
          refine ⟨964917766927501251947279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 643278511285000834631519 964917766927501251947279)
          ·
            refine ⟨1447376650391251877920919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 964917766927501251947279 1447376650391251877920919)
            ·
              refine ⟨2171064975586877816881379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1447376650391251877920919 2171064975586877816881379)
              ·
                refine ⟨3256597463380316725322069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2171064975586877816881379 3256597463380316725322069)
                ·
                  refine ⟨9540812880997021656217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 3256597463380316725322069 9540812880997021656217)
                  ·
                    rfl

theorem cell22_83613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 10].length) (baseStart_83613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_83613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_83613 prefixEnd_83613 := by exact prefixLift 83613
  have htrace : WordTrace (prefixWord ++ tailWord_83613) baseStart_83613 baseEnd_83613 := by
    simpa [prefixWord, tailWord_83613, baseEnd_83613] using wordTrace_append hprefix tailTrace_83613
  have hstable : (prefixWord ++ tailWord_83613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83613).length < 2 ^ (prefixWord ++ tailWord_83613).sum := by decide
  have hdescent : baseEnd_83613 < baseStart_83613 := by decide
  rcases family_descends (prefixWord ++ tailWord_83613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83732 : List Nat := [2, 4, 4, 1, 2, 1, 2, 2, 4]
def baseStart_83732 : Nat := 118140960795 + 83732 * 2 ^ 59
def prefixEnd_83732 : Nat := 4983230072969 + 3 ^ 40 * 83732 * 2
def baseEnd_83732 : Nat := 9554391591638140414429

theorem tailTrace_83732 : CollatzResearch.WordTrace tailWord_83732 prefixEnd_83732 9554391591638140414429 := by
  unfold tailWord_83732
  simp only [CollatzResearch.WordTrace]
  refine ⟨1526978466330369566102725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2035971288440492754803633 1526978466330369566102725)
  ·
    refine ⟨286308462436944293644261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1526978466330369566102725 286308462436944293644261)
    ·
      refine ⟨53682836706927055058299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 286308462436944293644261 53682836706927055058299)
      ·
        refine ⟨80524255060390582587449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53682836706927055058299 80524255060390582587449)
        ·
          refine ⟨60393191295292936940587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80524255060390582587449 60393191295292936940587)
          ·
            refine ⟨90589786942939405410881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60393191295292936940587 90589786942939405410881)
            ·
              refine ⟨67942340207204554058161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90589786942939405410881 67942340207204554058161)
              ·
                refine ⟨50956755155403415543621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67942340207204554058161 50956755155403415543621)
                ·
                  refine ⟨9554391591638140414429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50956755155403415543621 9554391591638140414429)
                  ·
                    rfl

theorem cell22_83732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_83732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_83732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_83732 prefixEnd_83732 := by exact prefixLift 83732
  have htrace : WordTrace (prefixWord ++ tailWord_83732) baseStart_83732 baseEnd_83732 := by
    simpa [prefixWord, tailWord_83732, baseEnd_83732] using wordTrace_append hprefix tailTrace_83732
  have hstable : (prefixWord ++ tailWord_83732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83732).length < 2 ^ (prefixWord ++ tailWord_83732).sum := by decide
  have hdescent : baseEnd_83732 < baseStart_83732 := by decide
  rcases family_descends (prefixWord ++ tailWord_83732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83752 : List Nat := [2, 1, 5, 1, 1, 3, 1, 1, 2, 5]
def baseStart_83752 : Nat := 118140960795 + 83752 * 2 ^ 59
def prefixEnd_83752 : Nat := 4983230072969 + 3 ^ 40 * 83752 * 2
def baseEnd_83752 : Nat := 28670021183641035743225

theorem tailTrace_83752 : CollatzResearch.WordTrace tailWord_83752 prefixEnd_83752 28670021183641035743225 := by
  unfold tailWord_83752
  simp only [CollatzResearch.WordTrace]
  refine ⟨1527343196294141273966755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2036457595058855031955673 1527343196294141273966755)
  ·
    refine ⟨2291014794441211910950133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1527343196294141273966755 2291014794441211910950133)
    ·
      refine ⟨214782636978863616651575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2291014794441211910950133 214782636978863616651575)
      ·
        refine ⟨322173955468295424977363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214782636978863616651575 322173955468295424977363)
        ·
          refine ⟨483260933202443137466045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 322173955468295424977363 483260933202443137466045)
          ·
            refine ⟨181222849950916176549767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 483260933202443137466045 181222849950916176549767)
            ·
              refine ⟨271834274926374264824651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181222849950916176549767 271834274926374264824651)
              ·
                refine ⟨407751412389561397236977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271834274926374264824651 407751412389561397236977)
                ·
                  refine ⟨305813559292171047927733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 407751412389561397236977 305813559292171047927733)
                  ·
                    refine ⟨28670021183641035743225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 305813559292171047927733 28670021183641035743225)
                    ·
                      rfl

theorem cell22_83752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_83752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_83752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_83752 prefixEnd_83752 := by exact prefixLift 83752
  have htrace : WordTrace (prefixWord ++ tailWord_83752) baseStart_83752 baseEnd_83752 := by
    simpa [prefixWord, tailWord_83752, baseEnd_83752] using wordTrace_append hprefix tailTrace_83752
  have hstable : (prefixWord ++ tailWord_83752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83752).length < 2 ^ (prefixWord ++ tailWord_83752).sum := by decide
  have hdescent : baseEnd_83752 < baseStart_83752 := by decide
  rcases family_descends (prefixWord ++ tailWord_83752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83784 : List Nat := [2, 1, 3, 1, 1, 4, 4, 1, 1, 4]
def baseStart_83784 : Nat := 118140960795 + 83784 * 2 ^ 59
def prefixEnd_83784 : Nat := 4983230072969 + 3 ^ 40 * 83784 * 2
def baseEnd_83784 : Nat := 28680975437603618943127

theorem tailTrace_83784 : CollatzResearch.WordTrace tailWord_83784 prefixEnd_83784 28680975437603618943127 := by
  unfold tailWord_83784
  simp only [CollatzResearch.WordTrace]
  refine ⟨1527926764236176006549203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2037235685648234675398937 1527926764236176006549203)
  ·
    refine ⟨2291890146354264009823805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1527926764236176006549203 2291890146354264009823805)
    ·
      refine ⟨859458804882849003683927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2291890146354264009823805 859458804882849003683927)
      ·
        refine ⟨1289188207324273505525891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 859458804882849003683927 1289188207324273505525891)
        ·
          refine ⟨1933782310986410258288837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1289188207324273505525891 1933782310986410258288837)
          ·
            refine ⟨362584183309951923429157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1933782310986410258288837 362584183309951923429157)
            ·
              refine ⟨67984534370615985642967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 362584183309951923429157 67984534370615985642967)
              ·
                refine ⟨101976801555923978464451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67984534370615985642967 101976801555923978464451)
                ·
                  refine ⟨152965202333885967696677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 101976801555923978464451 152965202333885967696677)
                  ·
                    refine ⟨28680975437603618943127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 152965202333885967696677 28680975437603618943127)
                    ·
                      rfl

theorem cell22_83784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 1, 4].length) (baseStart_83784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_83784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_83784 prefixEnd_83784 := by exact prefixLift 83784
  have htrace : WordTrace (prefixWord ++ tailWord_83784) baseStart_83784 baseEnd_83784 := by
    simpa [prefixWord, tailWord_83784, baseEnd_83784] using wordTrace_append hprefix tailTrace_83784
  have hstable : (prefixWord ++ tailWord_83784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83784).length < 2 ^ (prefixWord ++ tailWord_83784).sum := by decide
  have hdescent : baseEnd_83784 < baseStart_83784 := by decide
  rcases family_descends (prefixWord ++ tailWord_83784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83825 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 2, 7]
def baseStart_83825 : Nat := 118140960795 + 83825 * 2 ^ 59
def prefixEnd_83825 : Nat := 4983230072969 + 3 ^ 40 * 83825 * 2
def baseEnd_83825 : Nat := 28695010575493178668001

theorem tailTrace_83825 : CollatzResearch.WordTrace tailWord_83825 prefixEnd_83825 28695010575493178668001 := by
  unfold tailWord_83825
  simp only [CollatzResearch.WordTrace]
  refine ⟨3057348921323816015340929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2038232614215877343560619 3057348921323816015340929)
  ·
    refine ⟨2293011690992862011505697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3057348921323816015340929 2293011690992862011505697)
    ·
      refine ⟨1719758768244646508629273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2293011690992862011505697 1719758768244646508629273)
      ·
        refine ⟨1289819076183484881471955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1719758768244646508629273 1289819076183484881471955)
        ·
          refine ⟨1934728614275227322207933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1289819076183484881471955 1934728614275227322207933)
          ·
            refine ⟨725523230353210245827975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1934728614275227322207933 725523230353210245827975)
            ·
              refine ⟨1088284845529815368741963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 725523230353210245827975 1088284845529815368741963)
              ·
                refine ⟨1632427268294723053112945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1088284845529815368741963 1632427268294723053112945)
                ·
                  refine ⟨1224320451221042289834709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1632427268294723053112945 1224320451221042289834709)
                  ·
                    refine ⟨28695010575493178668001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1224320451221042289834709 28695010575493178668001)
                    ·
                      rfl

theorem cell22_83825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_83825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_83825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_83825 prefixEnd_83825 := by exact prefixLift 83825
  have htrace : WordTrace (prefixWord ++ tailWord_83825) baseStart_83825 baseEnd_83825 := by
    simpa [prefixWord, tailWord_83825, baseEnd_83825] using wordTrace_append hprefix tailTrace_83825
  have hstable : (prefixWord ++ tailWord_83825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83825).length < 2 ^ (prefixWord ++ tailWord_83825).sum := by decide
  have hdescent : baseEnd_83825 < baseStart_83825 := by decide
  rcases family_descends (prefixWord ++ tailWord_83825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83953 : List Nat := [1, 2, 2, 2, 5, 2, 2, 1, 1, 4]
def baseStart_83953 : Nat := 118140960795 + 83953 * 2 ^ 59
def prefixEnd_83953 : Nat := 4983230072969 + 3 ^ 40 * 83953 * 2
def baseEnd_83953 : Nat := 28738827591343511467609

theorem tailTrace_83953 : CollatzResearch.WordTrace tailWord_83953 prefixEnd_83953 28738827591343511467609 := by
  unfold tailWord_83953
  simp only [CollatzResearch.WordTrace]
  refine ⟨3062017464860093876000513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2041344976573395917333675 3062017464860093876000513)
  ·
    refine ⟨2296513098645070407000385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3062017464860093876000513 2296513098645070407000385)
    ·
      refine ⟨1722384823983802805250289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2296513098645070407000385 1722384823983802805250289)
      ·
        refine ⟨1291788617987852103937717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1722384823983802805250289 1291788617987852103937717)
        ·
          refine ⟨121105182936361134744161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1291788617987852103937717 121105182936361134744161)
          ·
            refine ⟨90828887202270851058121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121105182936361134744161 90828887202270851058121)
            ·
              refine ⟨68121665401703138293591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90828887202270851058121 68121665401703138293591)
              ·
                refine ⟨102182498102554707440387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68121665401703138293591 102182498102554707440387)
                ·
                  refine ⟨153273747153832061160581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102182498102554707440387 153273747153832061160581)
                  ·
                    refine ⟨28738827591343511467609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 153273747153832061160581 28738827591343511467609)
                    ·
                      rfl

theorem cell22_83953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 1, 4].length) (baseStart_83953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_83953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_83953 prefixEnd_83953 := by exact prefixLift 83953
  have htrace : WordTrace (prefixWord ++ tailWord_83953) baseStart_83953 baseEnd_83953 := by
    simpa [prefixWord, tailWord_83953, baseEnd_83953] using wordTrace_append hprefix tailTrace_83953
  have hstable : (prefixWord ++ tailWord_83953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83953).length < 2 ^ (prefixWord ++ tailWord_83953).sum := by decide
  have hdescent : baseEnd_83953 < baseStart_83953 := by decide
  rcases family_descends (prefixWord ++ tailWord_83953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83996 : List Nat := [2, 2, 3, 1, 3, 3, 2, 6]
def baseStart_83996 : Nat := 118140960795 + 83996 * 2 ^ 59
def prefixEnd_83996 : Nat := 4983230072969 + 3 ^ 40 * 83996 * 2
def baseEnd_83996 : Nat := 3194838596678414738053

theorem tailTrace_83996 : CollatzResearch.WordTrace tailWord_83996 prefixEnd_83996 3194838596678414738053 := by
  unfold tailWord_83996
  simp only [CollatzResearch.WordTrace]
  refine ⟨1531792901852156109907921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2042390535802874813210561 1531792901852156109907921)
  ·
    refine ⟨1148844676389117082430941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1531792901852156109907921 1148844676389117082430941)
    ·
      refine ⟨430816753645918905911603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1148844676389117082430941 430816753645918905911603)
      ·
        refine ⟨646225130468878358867405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 430816753645918905911603 646225130468878358867405)
        ·
          refine ⟨242334423925829384575277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 646225130468878358867405 242334423925829384575277)
          ·
            refine ⟨90875408972186019215729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 242334423925829384575277 90875408972186019215729)
            ·
              refine ⟨68156556729139514411797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90875408972186019215729 68156556729139514411797)
              ·
                refine ⟨3194838596678414738053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68156556729139514411797 3194838596678414738053)
                ·
                  rfl

theorem cell22_83996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 6].length) (baseStart_83996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_83996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_83996 prefixEnd_83996 := by exact prefixLift 83996
  have htrace : WordTrace (prefixWord ++ tailWord_83996) baseStart_83996 baseEnd_83996 := by
    simpa [prefixWord, tailWord_83996, baseEnd_83996] using wordTrace_append hprefix tailTrace_83996
  have hstable : (prefixWord ++ tailWord_83996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83996).length < 2 ^ (prefixWord ++ tailWord_83996).sum := by decide
  have hdescent : baseEnd_83996 < baseStart_83996 := by decide
  rcases family_descends (prefixWord ++ tailWord_83996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84011 : List Nat := [1, 1, 1, 1, 2, 1, 4, 7, 1, 3]
def baseStart_84011 : Nat := 118140960795 + 84011 * 2 ^ 59
def prefixEnd_84011 : Nat := 4983230072969 + 3 ^ 40 * 84011 * 2
def baseEnd_84011 : Nat := 28758682176650693517431

theorem tailTrace_84011 : CollatzResearch.WordTrace tailWord_84011 prefixEnd_84011 28758682176650693517431 := by
  unfold tailWord_84011
  simp only [CollatzResearch.WordTrace]
  refine ⟨3064132898649969781611887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2042755265766646521074591 3064132898649969781611887)
  ·
    refine ⟨4596199347974954672417831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3064132898649969781611887 4596199347974954672417831)
    ·
      refine ⟨6894299021962432008626747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4596199347974954672417831 6894299021962432008626747)
      ·
        refine ⟨10341448532943648012940121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6894299021962432008626747 10341448532943648012940121)
        ·
          refine ⟨7756086399707736009705091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10341448532943648012940121 7756086399707736009705091)
          ·
            refine ⟨11634129599561604014557637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7756086399707736009705091 11634129599561604014557637)
            ·
              refine ⟨2181399299917800752729557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11634129599561604014557637 2181399299917800752729557)
              ·
                refine ⟨51126546091823455142099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2181399299917800752729557 51126546091823455142099)
                ·
                  refine ⟨76689819137735182713149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51126546091823455142099 76689819137735182713149)
                  ·
                    refine ⟨28758682176650693517431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 76689819137735182713149 28758682176650693517431)
                    ·
                      rfl

theorem cell22_84011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 7, 1, 3].length) (baseStart_84011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_84011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_84011 prefixEnd_84011 := by exact prefixLift 84011
  have htrace : WordTrace (prefixWord ++ tailWord_84011) baseStart_84011 baseEnd_84011 := by
    simpa [prefixWord, tailWord_84011, baseEnd_84011] using wordTrace_append hprefix tailTrace_84011
  have hstable : (prefixWord ++ tailWord_84011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84011).length < 2 ^ (prefixWord ++ tailWord_84011).sum := by decide
  have hdescent : baseEnd_84011 < baseStart_84011 := by decide
  rcases family_descends (prefixWord ++ tailWord_84011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84037 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 2, 8]
def baseStart_84037 : Nat := 118140960795 + 84037 * 2 ^ 59
def prefixEnd_84037 : Nat := 4983230072969 + 3 ^ 40 * 84037 * 2
def baseEnd_84037 : Nat := 28767582507995292367351

theorem tailTrace_84037 : CollatzResearch.WordTrace tailWord_84037 prefixEnd_84037 28767582507995292367351 := by
  unfold tailWord_84037
  simp only [CollatzResearch.WordTrace]
  refine ⟨3065081196555776222058365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2043387464370517481372243 3065081196555776222058365)
  ·
    refine ⟨1149405448708416083271887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3065081196555776222058365 1149405448708416083271887)
    ·
      refine ⟨1724108173062624124907831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1149405448708416083271887 1724108173062624124907831)
      ·
        refine ⟨2586162259593936187361747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1724108173062624124907831 2586162259593936187361747)
        ·
          refine ⟨3879243389390904281042621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2586162259593936187361747 3879243389390904281042621)
          ·
            refine ⟨1454716271021589105390983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3879243389390904281042621 1454716271021589105390983)
            ·
              refine ⟨2182074406532383658086475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1454716271021589105390983 2182074406532383658086475)
              ·
                refine ⟨3273111609798575487129713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2182074406532383658086475 3273111609798575487129713)
                ·
                  refine ⟨2454833707348931615347285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3273111609798575487129713 2454833707348931615347285)
                  ·
                    refine ⟨28767582507995292367351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2454833707348931615347285 28767582507995292367351)
                    ·
                      rfl

theorem cell22_84037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_84037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_84037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_84037 prefixEnd_84037 := by exact prefixLift 84037
  have htrace : WordTrace (prefixWord ++ tailWord_84037) baseStart_84037 baseEnd_84037 := by
    simpa [prefixWord, tailWord_84037, baseEnd_84037] using wordTrace_append hprefix tailTrace_84037
  have hstable : (prefixWord ++ tailWord_84037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84037).length < 2 ^ (prefixWord ++ tailWord_84037).sum := by decide
  have hdescent : baseEnd_84037 < baseStart_84037 := by decide
  rcases family_descends (prefixWord ++ tailWord_84037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84101 : List Nat := [1, 3, 1, 1, 5, 2, 2, 1, 1, 5]
def baseStart_84101 : Nat := 118140960795 + 84101 * 2 ^ 59
def prefixEnd_84101 : Nat := 4983230072969 + 3 ^ 40 * 84101 * 2
def baseEnd_84101 : Nat := 28789491015920458767155

theorem tailTrace_84101 : CollatzResearch.WordTrace tailWord_84101 prefixEnd_84101 28789491015920458767155 := by
  unfold tailWord_84101
  simp only [CollatzResearch.WordTrace]
  refine ⟨3067415468323915152388157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2044943645549276768258771 3067415468323915152388157)
  ·
    refine ⟨1150280800621468182145559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3067415468323915152388157 1150280800621468182145559)
    ·
      refine ⟨1725421200932202273218339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1150280800621468182145559 1725421200932202273218339)
      ·
        refine ⟨2588131801398303409827509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1725421200932202273218339 2588131801398303409827509)
        ·
          refine ⟨242637356381090944671329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2588131801398303409827509 242637356381090944671329)
          ·
            refine ⟨181978017285818208503497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242637356381090944671329 181978017285818208503497)
            ·
              refine ⟨136483512964363656377623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181978017285818208503497 136483512964363656377623)
              ·
                refine ⟨204725269446545484566435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136483512964363656377623 204725269446545484566435)
                ·
                  refine ⟨307087904169818226849653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 204725269446545484566435 307087904169818226849653)
                  ·
                    refine ⟨28789491015920458767155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 307087904169818226849653 28789491015920458767155)
                    ·
                      rfl

theorem cell22_84101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 5].length) (baseStart_84101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_84101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_84101 prefixEnd_84101 := by exact prefixLift 84101
  have htrace : WordTrace (prefixWord ++ tailWord_84101) baseStart_84101 baseEnd_84101 := by
    simpa [prefixWord, tailWord_84101, baseEnd_84101] using wordTrace_append hprefix tailTrace_84101
  have hstable : (prefixWord ++ tailWord_84101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84101).length < 2 ^ (prefixWord ++ tailWord_84101).sum := by decide
  have hdescent : baseEnd_84101 < baseStart_84101 := by decide
  rcases family_descends (prefixWord ++ tailWord_84101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84122 : List Nat := [3, 1, 1, 5, 3, 1, 2, 1, 1, 4]
def baseStart_84122 : Nat := 118140960795 + 84122 * 2 ^ 59
def prefixEnd_84122 : Nat := 4983230072969 + 3 ^ 40 * 84122 * 2
def baseEnd_84122 : Nat := 28796679745083403992091

theorem tailTrace_84122 : CollatzResearch.WordTrace tailWord_84122 prefixEnd_84122 28796679745083403992091 := by
  unfold tailWord_84122
  simp only [CollatzResearch.WordTrace]
  refine ⟨767045350311958934725655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2045454267498557159268413 767045350311958934725655)
  ·
    refine ⟨1150568025467938402088483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 767045350311958934725655 1150568025467938402088483)
    ·
      refine ⟨1725852038201907603132725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1150568025467938402088483 1725852038201907603132725)
      ·
        refine ⟨161798628581428837793693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1725852038201907603132725 161798628581428837793693)
        ·
          refine ⟨60674485718035814172635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161798628581428837793693 60674485718035814172635)
          ·
            refine ⟨91011728577053721258953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60674485718035814172635 91011728577053721258953)
            ·
              refine ⟨68258796432790290944215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91011728577053721258953 68258796432790290944215)
              ·
                refine ⟨102388194649185436416323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68258796432790290944215 102388194649185436416323)
                ·
                  refine ⟨153582291973778154624485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102388194649185436416323 153582291973778154624485)
                  ·
                    refine ⟨28796679745083403992091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 153582291973778154624485 28796679745083403992091)
                    ·
                      rfl

theorem cell22_84122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 1, 4].length) (baseStart_84122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_84122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_84122 prefixEnd_84122 := by exact prefixLift 84122
  have htrace : WordTrace (prefixWord ++ tailWord_84122) baseStart_84122 baseEnd_84122 := by
    simpa [prefixWord, tailWord_84122, baseEnd_84122] using wordTrace_append hprefix tailTrace_84122
  have hstable : (prefixWord ++ tailWord_84122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84122).length < 2 ^ (prefixWord ++ tailWord_84122).sum := by decide
  have hdescent : baseEnd_84122 < baseStart_84122 := by decide
  rcases family_descends (prefixWord ++ tailWord_84122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84197 : List Nat := [1, 3, 1, 4, 2, 2, 3, 2, 1, 3]
def baseStart_84197 : Nat := 118140960795 + 84197 * 2 ^ 59
def prefixEnd_84197 : Nat := 4983230072969 + 3 ^ 40 * 84197 * 2
def baseEnd_84197 : Nat := 28822353777808208366861

theorem tailTrace_84197 : CollatzResearch.WordTrace tailWord_84197 prefixEnd_84197 28822353777808208366861 := by
  unfold tailWord_84197
  simp only [CollatzResearch.WordTrace]
  refine ⟨3070916875976123547882845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2047277917317415698588563 3070916875976123547882845)
  ·
    refine ⟨1151593828491046330456067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3070916875976123547882845 1151593828491046330456067)
    ·
      refine ⟨1727390742736569495684101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1151593828491046330456067 1727390742736569495684101)
      ·
        refine ⟨323885764263106780440769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1727390742736569495684101 323885764263106780440769)
        ·
          refine ⟨242914323197330085330577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323885764263106780440769 242914323197330085330577)
          ·
            refine ⟨182185742397997563997933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242914323197330085330577 182185742397997563997933)
            ·
              refine ⟨68319653399249086499225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182185742397997563997933 68319653399249086499225)
              ·
                refine ⟨51239740049436814874419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68319653399249086499225 51239740049436814874419)
                ·
                  refine ⟨76859610074155222311629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51239740049436814874419 76859610074155222311629)
                  ·
                    refine ⟨28822353777808208366861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 76859610074155222311629 28822353777808208366861)
                    ·
                      rfl

theorem cell22_84197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 2, 1, 3].length) (baseStart_84197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_84197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_84197 prefixEnd_84197 := by exact prefixLift 84197
  have htrace : WordTrace (prefixWord ++ tailWord_84197) baseStart_84197 baseEnd_84197 := by
    simpa [prefixWord, tailWord_84197, baseEnd_84197] using wordTrace_append hprefix tailTrace_84197
  have hstable : (prefixWord ++ tailWord_84197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84197).length < 2 ^ (prefixWord ++ tailWord_84197).sum := by decide
  have hdescent : baseEnd_84197 < baseStart_84197 := by decide
  rcases family_descends (prefixWord ++ tailWord_84197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84206 : List Nat := [4, 1, 2, 1, 1, 1, 1, 4, 3, 4]
def baseStart_84206 : Nat := 118140960795 + 84206 * 2 ^ 59
def prefixEnd_84206 : Nat := 4983230072969 + 3 ^ 40 * 84206 * 2
def baseEnd_84206 : Nat := 28825434661735184891833

theorem tailTrace_84206 : CollatzResearch.WordTrace tailWord_84206 prefixEnd_84206 28825434661735184891833 := by
  unfold tailWord_84206
  simp only [CollatzResearch.WordTrace]
  refine ⟨383905641617939760620059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2047496755295678723306981 383905641617939760620059)
  ·
    refine ⟨575858462426909640930089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 383905641617939760620059 575858462426909640930089)
    ·
      refine ⟨431893846820182230697567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 575858462426909640930089 431893846820182230697567)
      ·
        refine ⟨647840770230273346046351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431893846820182230697567 647840770230273346046351)
        ·
          refine ⟨971761155345410019069527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 647840770230273346046351 971761155345410019069527)
          ·
            refine ⟨1457641733018115028604291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 971761155345410019069527 1457641733018115028604291)
            ·
              refine ⟨2186462599527172542906437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1457641733018115028604291 2186462599527172542906437)
              ·
                refine ⟨409961737411344851794957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2186462599527172542906437 409961737411344851794957)
                ·
                  refine ⟨153735651529254319423109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 409961737411344851794957 153735651529254319423109)
                  ·
                    refine ⟨28825434661735184891833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 153735651529254319423109 28825434661735184891833)
                    ·
                      rfl

theorem cell22_84206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_84206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_84206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_84206 prefixEnd_84206 := by exact prefixLift 84206
  have htrace : WordTrace (prefixWord ++ tailWord_84206) baseStart_84206 baseEnd_84206 := by
    simpa [prefixWord, tailWord_84206, baseEnd_84206] using wordTrace_append hprefix tailTrace_84206
  have hstable : (prefixWord ++ tailWord_84206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84206).length < 2 ^ (prefixWord ++ tailWord_84206).sum := by decide
  have hdescent : baseEnd_84206 < baseStart_84206 := by decide
  rcases family_descends (prefixWord ++ tailWord_84206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84210 : List Nat := [3, 2, 1, 3, 2, 3, 2, 1, 5]
def baseStart_84210 : Nat := 118140960795 + 84210 * 2 ^ 59
def prefixEnd_84210 : Nat := 4983230072969 + 3 ^ 40 * 84210 * 2
def baseEnd_84210 : Nat := 9608934647826835930607

theorem tailTrace_84210 : CollatzResearch.WordTrace tailWord_84210 prefixEnd_84210 9608934647826835930607 := by
  unfold tailWord_84210
  simp only [CollatzResearch.WordTrace]
  refine ⟨767847756232256692026521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2047594016619351178737389 767847756232256692026521)
  ·
    refine ⟨575885817174192519019891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 767847756232256692026521 575885817174192519019891)
    ·
      refine ⟨863828725761288778529837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 575885817174192519019891 863828725761288778529837)
      ·
        refine ⟨323935772160483291948689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 863828725761288778529837 323935772160483291948689)
        ·
          refine ⟨242951829120362468961517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323935772160483291948689 242951829120362468961517)
          ·
            refine ⟨91106935920135925860569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 242951829120362468961517 91106935920135925860569)
            ·
              refine ⟨68330201940101944395427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91106935920135925860569 68330201940101944395427)
              ·
                refine ⟨102495302910152916593141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68330201940101944395427 102495302910152916593141)
                ·
                  refine ⟨9608934647826835930607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 102495302910152916593141 9608934647826835930607)
                  ·
                    rfl

theorem cell22_84210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 5].length) (baseStart_84210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_84210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_84210 prefixEnd_84210 := by exact prefixLift 84210
  have htrace : WordTrace (prefixWord ++ tailWord_84210) baseStart_84210 baseEnd_84210 := by
    simpa [prefixWord, tailWord_84210, baseEnd_84210] using wordTrace_append hprefix tailTrace_84210
  have hstable : (prefixWord ++ tailWord_84210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84210).length < 2 ^ (prefixWord ++ tailWord_84210).sum := by decide
  have hdescent : baseEnd_84210 < baseStart_84210 := by decide
  rcases family_descends (prefixWord ++ tailWord_84210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84219 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 7, 5]
def baseStart_84219 : Nat := 118140960795 + 84219 * 2 ^ 59
def prefixEnd_84219 : Nat := 4983230072969 + 3 ^ 40 * 84219 * 2
def baseEnd_84219 : Nat := 28829884827407484316793

theorem tailTrace_84219 : CollatzResearch.WordTrace tailWord_84219 prefixEnd_84219 28829884827407484316793 := by
  unfold tailWord_84219
  simp only [CollatzResearch.WordTrace]
  refine ⟨3071719281896421305183711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2047812854597614203455807 3071719281896421305183711)
  ·
    refine ⟨4607578922844631957775567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3071719281896421305183711 4607578922844631957775567)
    ·
      refine ⟨6911368384266947936663351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4607578922844631957775567 6911368384266947936663351)
      ·
        refine ⟨10367052576400421904995027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6911368384266947936663351 10367052576400421904995027)
        ·
          refine ⟨15550578864600632857492541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10367052576400421904995027 15550578864600632857492541)
          ·
            refine ⟨5831467074225237321559703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15550578864600632857492541 5831467074225237321559703)
            ·
              refine ⟨8747200611337855982339555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5831467074225237321559703 8747200611337855982339555)
              ·
                refine ⟨13120800917006783973509333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8747200611337855982339555 13120800917006783973509333)
                ·
                  refine ⟨307518771492346499379125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13120800917006783973509333 307518771492346499379125)
                  ·
                    refine ⟨28829884827407484316793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 307518771492346499379125 28829884827407484316793)
                    ·
                      rfl

theorem cell22_84219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 5].length) (baseStart_84219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_84219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_84219 prefixEnd_84219 := by exact prefixLift 84219
  have htrace : WordTrace (prefixWord ++ tailWord_84219) baseStart_84219 baseEnd_84219 := by
    simpa [prefixWord, tailWord_84219, baseEnd_84219] using wordTrace_append hprefix tailTrace_84219
  have hstable : (prefixWord ++ tailWord_84219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84219).length < 2 ^ (prefixWord ++ tailWord_84219).sum := by decide
  have hdescent : baseEnd_84219 < baseStart_84219 := by decide
  rcases family_descends (prefixWord ++ tailWord_84219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84236 : List Nat := [2, 2, 1, 2, 2, 2, 3, 2, 1, 5]
def baseStart_84236 : Nat := 118140960795 + 84236 * 2 ^ 59
def prefixEnd_84236 : Nat := 4983230072969 + 3 ^ 40 * 84236 * 2
def baseEnd_84236 : Nat := 28835704274825106641741

theorem tailTrace_84236 : CollatzResearch.WordTrace tailWord_84236 prefixEnd_84236 28835704274825106641741 := by
  unfold tailWord_84236
  simp only [CollatzResearch.WordTrace]
  refine ⟨1536169661417416604276281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2048226215223222139035041 1536169661417416604276281)
  ·
    refine ⟨1152127246063062453207211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1536169661417416604276281 1152127246063062453207211)
    ·
      refine ⟨1728190869094593679810817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1152127246063062453207211 1728190869094593679810817)
      ·
        refine ⟨1296143151820945259858113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1728190869094593679810817 1296143151820945259858113)
        ·
          refine ⟨972107363865708944893585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1296143151820945259858113 972107363865708944893585)
          ·
            refine ⟨729080522899281708670189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 972107363865708944893585 729080522899281708670189)
            ·
              refine ⟨273405196087230640751321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 729080522899281708670189 273405196087230640751321)
              ·
                refine ⟨205053897065422980563491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 273405196087230640751321 205053897065422980563491)
                ·
                  refine ⟨307580845598134470845237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 205053897065422980563491 307580845598134470845237)
                  ·
                    refine ⟨28835704274825106641741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 307580845598134470845237 28835704274825106641741)
                    ·
                      rfl

theorem cell22_84236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 1, 5].length) (baseStart_84236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_84236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_84236 prefixEnd_84236 := by exact prefixLift 84236
  have htrace : WordTrace (prefixWord ++ tailWord_84236) baseStart_84236 baseEnd_84236 := by
    simpa [prefixWord, tailWord_84236, baseEnd_84236] using wordTrace_append hprefix tailTrace_84236
  have hstable : (prefixWord ++ tailWord_84236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84236).length < 2 ^ (prefixWord ++ tailWord_84236).sum := by decide
  have hdescent : baseEnd_84236 < baseStart_84236 := by decide
  rcases family_descends (prefixWord ++ tailWord_84236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84238 : List Nat := [4, 1, 1, 2, 1, 2, 2, 5, 4]
def baseStart_84238 : Nat := 118140960795 + 84238 * 2 ^ 59
def prefixEnd_84238 : Nat := 4983230072969 + 3 ^ 40 * 84238 * 2
def baseEnd_84238 : Nat := 9612129638565922697245

theorem tailTrace_84238 : CollatzResearch.WordTrace tailWord_84238 prefixEnd_84238 9612129638565922697245 := by
  unfold tailWord_84238
  simp only [CollatzResearch.WordTrace]
  refine ⟨384051533603448443765671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2048274845885058366750245 384051533603448443765671)
  ·
    refine ⟨576077300405172665648507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 384051533603448443765671 576077300405172665648507)
    ·
      refine ⟨864115950607758998472761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 576077300405172665648507 864115950607758998472761)
      ·
        refine ⟨648086962955819248854571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 864115950607758998472761 648086962955819248854571)
        ·
          refine ⟨972130444433728873281857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 648086962955819248854571 972130444433728873281857)
          ·
            refine ⟨729097833325296654961393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 972130444433728873281857 729097833325296654961393)
            ·
              refine ⟨546823374993972491221045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 729097833325296654961393 546823374993972491221045)
              ·
                refine ⟨51264691405684921051973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 546823374993972491221045 51264691405684921051973)
                ·
                  refine ⟨9612129638565922697245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51264691405684921051973 9612129638565922697245)
                  ·
                    rfl

theorem cell22_84238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 5, 4].length) (baseStart_84238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_84238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_84238 prefixEnd_84238 := by exact prefixLift 84238
  have htrace : WordTrace (prefixWord ++ tailWord_84238) baseStart_84238 baseEnd_84238 := by
    simpa [prefixWord, tailWord_84238, baseEnd_84238] using wordTrace_append hprefix tailTrace_84238
  have hstable : (prefixWord ++ tailWord_84238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84238).length < 2 ^ (prefixWord ++ tailWord_84238).sum := by decide
  have hdescent : baseEnd_84238 < baseStart_84238 := by decide
  rcases family_descends (prefixWord ++ tailWord_84238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84251 : List Nat := [1, 1, 1, 1, 1, 1, 8, 2, 2, 4]
def baseStart_84251 : Nat := 118140960795 + 84251 * 2 ^ 59
def prefixEnd_84251 : Nat := 4983230072969 + 3 ^ 40 * 84251 * 2
def baseEnd_84251 : Nat := 28840839081370067516695

theorem tailTrace_84251 : CollatzResearch.WordTrace tailWord_84251 prefixEnd_84251 28840839081370067516695 := by
  unfold tailWord_84251
  simp only [CollatzResearch.WordTrace]
  refine ⟨3072886417780490770348607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2048590945186993846899071 3072886417780490770348607)
  ·
    refine ⟨4609329626670736155522911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3072886417780490770348607 4609329626670736155522911)
    ·
      refine ⟨6913994440006104233284367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4609329626670736155522911 6913994440006104233284367)
      ·
        refine ⟨10370991660009156349926551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6913994440006104233284367 10370991660009156349926551)
        ·
          refine ⟨15556487490013734524889827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10370991660009156349926551 15556487490013734524889827)
          ·
            refine ⟨23334731235020601787334741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15556487490013734524889827 23334731235020601787334741)
            ·
              refine ⟨273453881660397677195329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 23334731235020601787334741 273453881660397677195329)
              ·
                refine ⟨205090411245298257896497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 273453881660397677195329 205090411245298257896497)
                ·
                  refine ⟨153817808433973693422373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 205090411245298257896497 153817808433973693422373)
                  ·
                    refine ⟨28840839081370067516695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 153817808433973693422373 28840839081370067516695)
                    ·
                      rfl

theorem cell22_84251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 2, 4].length) (baseStart_84251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_84251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_84251 prefixEnd_84251 := by exact prefixLift 84251
  have htrace : WordTrace (prefixWord ++ tailWord_84251) baseStart_84251 baseEnd_84251 := by
    simpa [prefixWord, tailWord_84251, baseEnd_84251] using wordTrace_append hprefix tailTrace_84251
  have hstable : (prefixWord ++ tailWord_84251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84251).length < 2 ^ (prefixWord ++ tailWord_84251).sum := by decide
  have hdescent : baseEnd_84251 < baseStart_84251 := by decide
  rcases family_descends (prefixWord ++ tailWord_84251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84255 : List Nat := [1, 1, 2, 4, 3, 1, 4, 2, 4]
def baseStart_84255 : Nat := 118140960795 + 84255 * 2 ^ 59
def prefixEnd_84255 : Nat := 4983230072969 + 3 ^ 40 * 84255 * 2
def baseEnd_84255 : Nat := 9614069454371796805561

theorem tailTrace_84255 : CollatzResearch.WordTrace tailWord_84255 prefixEnd_84255 9614069454371796805561 := by
  unfold tailWord_84255
  simp only [CollatzResearch.WordTrace]
  refine ⟨3073032309765999453494219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2048688206510666302329479 3073032309765999453494219)
  ·
    refine ⟨4609548464648999180241329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3073032309765999453494219 4609548464648999180241329)
    ·
      refine ⟨3457161348486749385180997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4609548464648999180241329 3457161348486749385180997)
      ·
        refine ⟨648217752841265509721437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3457161348486749385180997 648217752841265509721437)
        ·
          refine ⟨243081657315474566145539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 648217752841265509721437 243081657315474566145539)
          ·
            refine ⟨364622485973211849218309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243081657315474566145539 364622485973211849218309)
            ·
              refine ⟨68366716119977221728433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 364622485973211849218309 68366716119977221728433)
              ·
                refine ⟨51275037089982916296325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68366716119977221728433 51275037089982916296325)
                ·
                  refine ⟨9614069454371796805561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51275037089982916296325 9614069454371796805561)
                  ·
                    rfl

theorem cell22_84255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 2, 4].length) (baseStart_84255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_84255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_84255 prefixEnd_84255 := by exact prefixLift 84255
  have htrace : WordTrace (prefixWord ++ tailWord_84255) baseStart_84255 baseEnd_84255 := by
    simpa [prefixWord, tailWord_84255, baseEnd_84255] using wordTrace_append hprefix tailTrace_84255
  have hstable : (prefixWord ++ tailWord_84255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84255).length < 2 ^ (prefixWord ++ tailWord_84255).sum := by decide
  have hdescent : baseEnd_84255 < baseStart_84255 := by decide
  rcases family_descends (prefixWord ++ tailWord_84255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84311 : List Nat := [1, 1, 3, 2, 3, 1, 3, 1, 7]
def baseStart_84311 : Nat := 118140960795 + 84311 * 2 ^ 59
def prefixEnd_84311 : Nat := 4983230072969 + 3 ^ 40 * 84311 * 2
def baseEnd_84311 : Nat := 9620459435849970338837

theorem tailTrace_84311 : CollatzResearch.WordTrace tailWord_84311 prefixEnd_84311 9620459435849970338837 := by
  unfold tailWord_84311
  simp only [CollatzResearch.WordTrace]
  refine ⟨3075074797563121017532787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2050049865042080678355191 3075074797563121017532787)
  ·
    refine ⟨4612612196344681526299181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3075074797563121017532787 4612612196344681526299181)
    ·
      refine ⟨1729729573629255572362193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4612612196344681526299181 1729729573629255572362193)
      ·
        refine ⟨1297297180221941679271645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1729729573629255572362193 1297297180221941679271645)
        ·
          refine ⟨486486442583228129726867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1297297180221941679271645 486486442583228129726867)
          ·
            refine ⟨729729663874842194590301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 486486442583228129726867 729729663874842194590301)
            ·
              refine ⟨273648623953065822971363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 729729663874842194590301 273648623953065822971363)
              ·
                refine ⟨410472935929598734457045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 273648623953065822971363 410472935929598734457045)
                ·
                  refine ⟨9620459435849970338837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 410472935929598734457045 9620459435849970338837)
                  ·
                    rfl

theorem cell22_84311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 7].length) (baseStart_84311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_84311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_84311 prefixEnd_84311 := by exact prefixLift 84311
  have htrace : WordTrace (prefixWord ++ tailWord_84311) baseStart_84311 baseEnd_84311 := by
    simpa [prefixWord, tailWord_84311, baseEnd_84311] using wordTrace_append hprefix tailTrace_84311
  have hstable : (prefixWord ++ tailWord_84311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84311).length < 2 ^ (prefixWord ++ tailWord_84311).sum := by decide
  have hdescent : baseEnd_84311 < baseStart_84311 := by decide
  rcases family_descends (prefixWord ++ tailWord_84311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84392 : List Nat := [2, 1, 6, 1, 1, 1, 3, 2, 1, 4]
def baseStart_84392 : Nat := 118140960795 + 84392 * 2 ^ 59
def prefixEnd_84392 : Nat := 4983230072969 + 3 ^ 40 * 84392 * 2
def baseEnd_84392 : Nat := 28889106262892699741263

theorem tailTrace_84392 : CollatzResearch.WordTrace tailWord_84392 prefixEnd_84392 28889106262892699741263 := by
  unfold tailWord_84392
  simp only [CollatzResearch.WordTrace]
  refine ⟨1539014555134835925615715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2052019406846447900820953 1539014555134835925615715)
  ·
    refine ⟨2308521832702253888423573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1539014555134835925615715 2308521832702253888423573)
    ·
      refine ⟨108211960907918151019855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2308521832702253888423573 108211960907918151019855)
      ·
        refine ⟨162317941361877226529783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108211960907918151019855 162317941361877226529783)
        ·
          refine ⟨243476912042815839794675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162317941361877226529783 243476912042815839794675)
          ·
            refine ⟨365215368064223759692013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243476912042815839794675 365215368064223759692013)
            ·
              refine ⟨136955763024083909884505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 365215368064223759692013 136955763024083909884505)
              ·
                refine ⟨102716822268062932413379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136955763024083909884505 102716822268062932413379)
                ·
                  refine ⟨154075233402094398620069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102716822268062932413379 154075233402094398620069)
                  ·
                    refine ⟨28889106262892699741263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 154075233402094398620069 28889106262892699741263)
                    ·
                      rfl

theorem cell22_84392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_84392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_84392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_84392 prefixEnd_84392 := by exact prefixLift 84392
  have htrace : WordTrace (prefixWord ++ tailWord_84392) baseStart_84392 baseEnd_84392 := by
    simpa [prefixWord, tailWord_84392, baseEnd_84392] using wordTrace_append hprefix tailTrace_84392
  have hstable : (prefixWord ++ tailWord_84392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84392).length < 2 ^ (prefixWord ++ tailWord_84392).sum := by decide
  have hdescent : baseEnd_84392 < baseStart_84392 := by decide
  rcases family_descends (prefixWord ++ tailWord_84392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84405 : List Nat := [1, 3, 3, 2, 3, 1, 1, 2, 1, 5]
def baseStart_84405 : Nat := 118140960795 + 84405 * 2 ^ 59
def prefixEnd_84405 : Nat := 4983230072969 + 3 ^ 40 * 84405 * 2
def baseEnd_84405 : Nat := 28893556428564999166223

theorem tailTrace_84405 : CollatzResearch.WordTrace tailWord_84405 prefixEnd_84405 28893556428564999166223 := by
  unfold tailWord_84405
  simp only [CollatzResearch.WordTrace]
  refine ⟨3078503259222575071454669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2052335506148383380969779 3078503259222575071454669)
  ·
    refine ⟨1154438722208465651795501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3078503259222575071454669 1154438722208465651795501)
    ·
      refine ⟨432914520828174619423313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1154438722208465651795501 432914520828174619423313)
      ·
        refine ⟨324685890621130964567485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 432914520828174619423313 324685890621130964567485)
        ·
          refine ⟨121757208982924111712807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 324685890621130964567485 121757208982924111712807)
          ·
            refine ⟨182635813474386167569211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121757208982924111712807 182635813474386167569211)
            ·
              refine ⟨273953720211579251353817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182635813474386167569211 273953720211579251353817)
              ·
                refine ⟨205465290158684438515363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 273953720211579251353817 205465290158684438515363)
                ·
                  refine ⟨308197935238026657773045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 205465290158684438515363 308197935238026657773045)
                  ·
                    refine ⟨28893556428564999166223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 308197935238026657773045 28893556428564999166223)
                    ·
                      rfl

theorem cell22_84405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_84405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_84405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_84405 prefixEnd_84405 := by exact prefixLift 84405
  have htrace : WordTrace (prefixWord ++ tailWord_84405) baseStart_84405 baseEnd_84405 := by
    simpa [prefixWord, tailWord_84405, baseEnd_84405] using wordTrace_append hprefix tailTrace_84405
  have hstable : (prefixWord ++ tailWord_84405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84405).length < 2 ^ (prefixWord ++ tailWord_84405).sum := by decide
  have hdescent : baseEnd_84405 < baseStart_84405 := by decide
  rcases family_descends (prefixWord ++ tailWord_84405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84433 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 7, 3]
def baseStart_84433 : Nat := 118140960795 + 84433 * 2 ^ 59
def prefixEnd_84433 : Nat := 4983230072969 + 3 ^ 40 * 84433 * 2
def baseEnd_84433 : Nat := 28903141400782259466137

theorem tailTrace_84433 : CollatzResearch.WordTrace tailWord_84433 prefixEnd_84433 28903141400782259466137 := by
  unfold tailWord_84433
  simp only [CollatzResearch.WordTrace]
  refine ⟨3079524503121135853473953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2053016335414090568982635 3079524503121135853473953)
  ·
    refine ⟨2309643377340851890105465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3079524503121135853473953 2309643377340851890105465)
    ·
      refine ⟨1732232533005638917579099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2309643377340851890105465 1732232533005638917579099)
      ·
        refine ⟨2598348799508458376368649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1732232533005638917579099 2598348799508458376368649)
        ·
          refine ⟨1948761599631343782276487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2598348799508458376368649 1948761599631343782276487)
          ·
            refine ⟨2923142399447015673414731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1948761599631343782276487 2923142399447015673414731)
            ·
              refine ⟨4384713599170523510122097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2923142399447015673414731 4384713599170523510122097)
              ·
                refine ⟨3288535199377892632591573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4384713599170523510122097 3288535199377892632591573)
                ·
                  refine ⟨77075043735419358576365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3288535199377892632591573 77075043735419358576365)
                  ·
                    refine ⟨28903141400782259466137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77075043735419358576365 28903141400782259466137)
                    ·
                      rfl

theorem cell22_84433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 7, 3].length) (baseStart_84433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_84433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_84433 prefixEnd_84433 := by exact prefixLift 84433
  have htrace : WordTrace (prefixWord ++ tailWord_84433) baseStart_84433 baseEnd_84433 := by
    simpa [prefixWord, tailWord_84433, baseEnd_84433] using wordTrace_append hprefix tailTrace_84433
  have hstable : (prefixWord ++ tailWord_84433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84433).length < 2 ^ (prefixWord ++ tailWord_84433).sum := by decide
  have hdescent : baseEnd_84433 < baseStart_84433 := by decide
  rcases family_descends (prefixWord ++ tailWord_84433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84467 : List Nat := [1, 1, 1, 2, 2, 2, 6, 3, 1, 3]
def baseStart_84467 : Nat := 118140960795 + 84467 * 2 ^ 59
def prefixEnd_84467 : Nat := 4983230072969 + 3 ^ 40 * 84467 * 2
def baseEnd_84467 : Nat := 28914780295617504116033

theorem tailTrace_84467 : CollatzResearch.WordTrace tailWord_84467 prefixEnd_84467 28914780295617504116033 := by
  unfold tailWord_84467
  simp only [CollatzResearch.WordTrace]
  refine ⟨3080764584997959660211655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2053843056665306440141103 3080764584997959660211655)
  ·
    refine ⟨4621146877496939490317483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3080764584997959660211655 4621146877496939490317483)
    ·
      refine ⟨6931720316245409235476225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4621146877496939490317483 6931720316245409235476225)
      ·
        refine ⟨5198790237184056926607169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6931720316245409235476225 5198790237184056926607169)
        ·
          refine ⟨3899092677888042694955377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5198790237184056926607169 3899092677888042694955377)
          ·
            refine ⟨2924319508416032021216533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3899092677888042694955377 2924319508416032021216533)
            ·
              refine ⟨137077476957001500994525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2924319508416032021216533 137077476957001500994525)
              ·
                refine ⟨51404053858875562872947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137077476957001500994525 51404053858875562872947)
                ·
                  refine ⟨77106080788313344309421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51404053858875562872947 77106080788313344309421)
                  ·
                    refine ⟨28914780295617504116033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77106080788313344309421 28914780295617504116033)
                    ·
                      rfl

theorem cell22_84467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 3, 1, 3].length) (baseStart_84467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_84467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_84467 prefixEnd_84467 := by exact prefixLift 84467
  have htrace : WordTrace (prefixWord ++ tailWord_84467) baseStart_84467 baseEnd_84467 := by
    simpa [prefixWord, tailWord_84467, baseEnd_84467] using wordTrace_append hprefix tailTrace_84467
  have hstable : (prefixWord ++ tailWord_84467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84467).length < 2 ^ (prefixWord ++ tailWord_84467).sum := by decide
  have hdescent : baseEnd_84467 < baseStart_84467 := by decide
  rcases family_descends (prefixWord ++ tailWord_84467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84484 : List Nat := [2, 3, 2, 3, 1, 1, 2, 4, 1, 3]
def baseStart_84484 : Nat := 118140960795 + 84484 * 2 ^ 59
def prefixEnd_84484 : Nat := 4983230072969 + 3 ^ 40 * 84484 * 2
def baseEnd_84484 : Nat := 28920599743035126440981

theorem tailTrace_84484 : CollatzResearch.WordTrace tailWord_84484 prefixEnd_84484 28920599743035126440981 := by
  unfold tailWord_84484
  simp only [CollatzResearch.WordTrace]
  refine ⟨1540692312968185781790253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2054256417290914375720337 1540692312968185781790253)
  ·
    refine ⟨577759617363069668171345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1540692312968185781790253 577759617363069668171345)
    ·
      refine ⟨433319713022302251128509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 577759617363069668171345 433319713022302251128509)
      ·
        refine ⟨162494892383363344173191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 433319713022302251128509 162494892383363344173191)
        ·
          refine ⟨243742338575045016259787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162494892383363344173191 243742338575045016259787)
          ·
            refine ⟨365613507862567524389681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243742338575045016259787 365613507862567524389681)
            ·
              refine ⟨274210130896925643292261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 365613507862567524389681 274210130896925643292261)
              ·
                refine ⟨51414399543173558117299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 274210130896925643292261 51414399543173558117299)
                ·
                  refine ⟨77121599314760337175949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51414399543173558117299 77121599314760337175949)
                  ·
                    refine ⟨28920599743035126440981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77121599314760337175949 28920599743035126440981)
                    ·
                      rfl

theorem cell22_84484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_84484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_84484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_84484 prefixEnd_84484 := by exact prefixLift 84484
  have htrace : WordTrace (prefixWord ++ tailWord_84484) baseStart_84484 baseEnd_84484 := by
    simpa [prefixWord, tailWord_84484, baseEnd_84484] using wordTrace_append hprefix tailTrace_84484
  have hstable : (prefixWord ++ tailWord_84484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84484).length < 2 ^ (prefixWord ++ tailWord_84484).sum := by decide
  have hdescent : baseEnd_84484 < baseStart_84484 := by decide
  rcases family_descends (prefixWord ++ tailWord_84484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84523 : List Nat := [1, 1, 1, 1, 2, 1, 3, 6, 1, 5]
def baseStart_84523 : Nat := 118140960795 + 84523 * 2 ^ 59
def prefixEnd_84523 : Nat := 4983230072969 + 3 ^ 40 * 84523 * 2
def baseEnd_84523 : Nat := 28933950240052024715861

theorem tailTrace_84523 : CollatzResearch.WordTrace tailWord_84523 prefixEnd_84523 28933950240052024715861 := by
  unfold tailWord_84523
  simp only [CollatzResearch.WordTrace]
  refine ⟨3082807072795081224250223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2055204715196720816166815 3082807072795081224250223)
  ·
    refine ⟨4624210609192621836375335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3082807072795081224250223 4624210609192621836375335)
    ·
      refine ⟨6936315913788932754563003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4624210609192621836375335 6936315913788932754563003)
      ·
        refine ⟨10404473870683399131844505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6936315913788932754563003 10404473870683399131844505)
        ·
          refine ⟨7803355403012549348883379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10404473870683399131844505 7803355403012549348883379)
          ·
            refine ⟨11705033104518824023325069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7803355403012549348883379 11705033104518824023325069)
            ·
              refine ⟨4389387414194559008746901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11705033104518824023325069 4389387414194559008746901)
              ·
                refine ⟨205752535040369953535011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4389387414194559008746901 205752535040369953535011)
                ·
                  refine ⟨308628802560554930302517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 205752535040369953535011 308628802560554930302517)
                  ·
                    refine ⟨28933950240052024715861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 308628802560554930302517 28933950240052024715861)
                    ·
                      rfl

theorem cell22_84523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 5].length) (baseStart_84523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_84523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_84523 prefixEnd_84523 := by exact prefixLift 84523
  have htrace : WordTrace (prefixWord ++ tailWord_84523) baseStart_84523 baseEnd_84523 := by
    simpa [prefixWord, tailWord_84523, baseEnd_84523] using wordTrace_append hprefix tailTrace_84523
  have hstable : (prefixWord ++ tailWord_84523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84523).length < 2 ^ (prefixWord ++ tailWord_84523).sum := by decide
  have hdescent : baseEnd_84523 < baseStart_84523 := by decide
  rcases family_descends (prefixWord ++ tailWord_84523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84548 : List Nat := [2, 3, 5, 1, 1, 2, 2, 1, 5]
def baseStart_84548 : Nat := 118140960795 + 84548 * 2 ^ 59
def prefixEnd_84548 : Nat := 4983230072969 + 3 ^ 40 * 84548 * 2
def baseEnd_84548 : Nat := 9647502750320097613595

theorem tailTrace_84548 : CollatzResearch.WordTrace tailWord_84548 prefixEnd_84548 9647502750320097613595 := by
  unfold tailWord_84548
  simp only [CollatzResearch.WordTrace]
  refine ⟨1541859448852255246955149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2055812598469673662606865 1541859448852255246955149)
  ·
    refine ⟨578197293319595717608181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1541859448852255246955149 578197293319595717608181)
    ·
      refine ⟨54205996248712098525767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 578197293319595717608181 54205996248712098525767)
      ·
        refine ⟨81308994373068147788651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54205996248712098525767 81308994373068147788651)
        ·
          refine ⟨121963491559602221682977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81308994373068147788651 121963491559602221682977)
          ·
            refine ⟨91472618669701666262233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121963491559602221682977 91472618669701666262233)
            ·
              refine ⟨68604464002276249696675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91472618669701666262233 68604464002276249696675)
              ·
                refine ⟨102906696003414374545013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68604464002276249696675 102906696003414374545013)
                ·
                  refine ⟨9647502750320097613595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 102906696003414374545013 9647502750320097613595)
                  ·
                    rfl

theorem cell22_84548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 5].length) (baseStart_84548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_84548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_84548 prefixEnd_84548 := by exact prefixLift 84548
  have htrace : WordTrace (prefixWord ++ tailWord_84548) baseStart_84548 baseEnd_84548 := by
    simpa [prefixWord, tailWord_84548, baseEnd_84548] using wordTrace_append hprefix tailTrace_84548
  have hstable : (prefixWord ++ tailWord_84548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84548).length < 2 ^ (prefixWord ++ tailWord_84548).sum := by decide
  have hdescent : baseEnd_84548 < baseStart_84548 := by decide
  rcases family_descends (prefixWord ++ tailWord_84548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84568 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 2, 7]
def baseStart_84568 : Nat := 118140960795 + 84568 * 2 ^ 59
def prefixEnd_84568 : Nat := 4983230072969 + 3 ^ 40 * 84568 * 2
def baseEnd_84568 : Nat := 28949354659686907340723

theorem tailTrace_84568 : CollatzResearch.WordTrace tailWord_84568 prefixEnd_84568 28949354659686907340723 := by
  unfold tailWord_84568
  simp only [CollatzResearch.WordTrace]
  refine ⟨1542224178816026954819179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2056298905088035939758905 1542224178816026954819179)
  ·
    refine ⟨2313336268224040432228769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1542224178816026954819179 2313336268224040432228769)
    ·
      refine ⟨1735002201168030324171577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2313336268224040432228769 1735002201168030324171577)
      ·
        refine ⟨1301251650876022743128683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1735002201168030324171577 1301251650876022743128683)
        ·
          refine ⟨1951877476314034114693025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1301251650876022743128683 1951877476314034114693025)
          ·
            refine ⟨1463908107235525586019769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1951877476314034114693025 1463908107235525586019769)
            ·
              refine ⟨1097931080426644189514827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1463908107235525586019769 1097931080426644189514827)
              ·
                refine ⟨1646896620639966284272241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1097931080426644189514827 1646896620639966284272241)
                ·
                  refine ⟨1235172465479974713204181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1646896620639966284272241 1235172465479974713204181)
                  ·
                    refine ⟨28949354659686907340723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1235172465479974713204181 28949354659686907340723)
                    ·
                      rfl

theorem cell22_84568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_84568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_84568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_84568 prefixEnd_84568 := by exact prefixLift 84568
  have htrace : WordTrace (prefixWord ++ tailWord_84568) baseStart_84568 baseEnd_84568 := by
    simpa [prefixWord, tailWord_84568, baseEnd_84568] using wordTrace_append hprefix tailTrace_84568
  have hstable : (prefixWord ++ tailWord_84568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84568).length < 2 ^ (prefixWord ++ tailWord_84568).sum := by decide
  have hdescent : baseEnd_84568 < baseStart_84568 := by decide
  rcases family_descends (prefixWord ++ tailWord_84568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84615 : List Nat := [1, 1, 4, 2, 1, 2, 1, 5, 5]
def baseStart_84615 : Nat := 118140960795 + 84615 * 2 ^ 59
def prefixEnd_84615 : Nat := 4983230072969 + 3 ^ 40 * 84615 * 2
def baseEnd_84615 : Nat := 9655147906731483805193

theorem tailTrace_84615 : CollatzResearch.WordTrace tailWord_84615 prefixEnd_84615 9655147906731483805193 := by
  unfold tailWord_84615
  simp only [CollatzResearch.WordTrace]
  refine ⟨3086162588461780936599299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2057441725641187291066199 3086162588461780936599299)
  ·
    refine ⟨4629243882692671404898949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3086162588461780936599299 4629243882692671404898949)
    ·
      refine ⟨867983228004875888418553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4629243882692671404898949 867983228004875888418553)
      ·
        refine ⟨650987421003656916313915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 867983228004875888418553 650987421003656916313915)
        ·
          refine ⟨976481131505485374470873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 650987421003656916313915 976481131505485374470873)
          ·
            refine ⟨732360848629114030853155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 976481131505485374470873 732360848629114030853155)
            ·
              refine ⟨1098541272943671046279733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 732360848629114030853155 1098541272943671046279733)
              ·
                refine ⟨102988244338469160588725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1098541272943671046279733 102988244338469160588725)
                ·
                  refine ⟨9655147906731483805193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 102988244338469160588725 9655147906731483805193)
                  ·
                    rfl

theorem cell22_84615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 5].length) (baseStart_84615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_84615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_84615 prefixEnd_84615 := by exact prefixLift 84615
  have htrace : WordTrace (prefixWord ++ tailWord_84615) baseStart_84615 baseEnd_84615 := by
    simpa [prefixWord, tailWord_84615, baseEnd_84615] using wordTrace_append hprefix tailTrace_84615
  have hstable : (prefixWord ++ tailWord_84615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84615).length < 2 ^ (prefixWord ++ tailWord_84615).sum := by decide
  have hdescent : baseEnd_84615 < baseStart_84615 := by decide
  rcases family_descends (prefixWord ++ tailWord_84615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84636 : List Nat := [2, 2, 3, 2, 2, 2, 2, 3, 1, 3]
def baseStart_84636 : Nat := 118140960795 + 84636 * 2 ^ 59
def prefixEnd_84636 : Nat := 4983230072969 + 3 ^ 40 * 84636 * 2
def baseEnd_84636 : Nat := 28972632449357396640515

theorem tailTrace_84636 : CollatzResearch.WordTrace tailWord_84636 prefixEnd_84636 28972632449357396640515 := by
  unfold tailWord_84636
  simp only [CollatzResearch.WordTrace]
  refine ⟨1543464260692850761556881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2057952347590467682075841 1543464260692850761556881)
  ·
    refine ⟨1157598195519638071167661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1543464260692850761556881 1157598195519638071167661)
    ·
      refine ⟨434099323319864276687873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1157598195519638071167661 434099323319864276687873)
      ·
        refine ⟨325574492489898207515905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 434099323319864276687873 325574492489898207515905)
        ·
          refine ⟨244180869367423655636929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 325574492489898207515905 244180869367423655636929)
          ·
            refine ⟨183135652025567741727697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 244180869367423655636929 183135652025567741727697)
            ·
              refine ⟨137351739019175806295773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183135652025567741727697 137351739019175806295773)
              ·
                refine ⟨51506902132190927360915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137351739019175806295773 51506902132190927360915)
                ·
                  refine ⟨77260353198286391041373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51506902132190927360915 77260353198286391041373)
                  ·
                    refine ⟨28972632449357396640515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77260353198286391041373 28972632449357396640515)
                    ·
                      rfl

theorem cell22_84636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_84636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_84636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_84636 prefixEnd_84636 := by exact prefixLift 84636
  have htrace : WordTrace (prefixWord ++ tailWord_84636) baseStart_84636 baseEnd_84636 := by
    simpa [prefixWord, tailWord_84636, baseEnd_84636] using wordTrace_append hprefix tailTrace_84636
  have hstable : (prefixWord ++ tailWord_84636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84636).length < 2 ^ (prefixWord ++ tailWord_84636).sum := by decide
  have hdescent : baseEnd_84636 < baseStart_84636 := by decide
  rcases family_descends (prefixWord ++ tailWord_84636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84705 : List Nat := [1, 2, 3, 1, 4, 1, 10]
def baseStart_84705 : Nat := 118140960795 + 84705 * 2 ^ 59
def prefixEnd_84705 : Nat := 4983230072969 + 3 ^ 40 * 84705 * 2
def baseEnd_84705 : Nat := 1073935279980156172789

theorem tailTrace_84705 : CollatzResearch.WordTrace tailWord_84705 prefixEnd_84705 1073935279980156172789 := by
  unfold tailWord_84705
  simp only [CollatzResearch.WordTrace]
  refine ⟨3089445158135726307375569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2059630105423817538250379 3089445158135726307375569)
  ·
    refine ⟨2317083868601794730531677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3089445158135726307375569 2317083868601794730531677)
    ·
      refine ⟨868906450725673023949379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2317083868601794730531677 868906450725673023949379)
      ·
        refine ⟨1303359676088509535924069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 868906450725673023949379 1303359676088509535924069)
        ·
          refine ⟨244379939266595537985763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1303359676088509535924069 244379939266595537985763)
          ·
            refine ⟨366569908899893306978645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244379939266595537985763 366569908899893306978645)
            ·
              refine ⟨1073935279980156172789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 366569908899893306978645 1073935279980156172789)
              ·
                rfl

theorem cell22_84705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 10].length) (baseStart_84705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_84705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_84705 prefixEnd_84705 := by exact prefixLift 84705
  have htrace : WordTrace (prefixWord ++ tailWord_84705) baseStart_84705 baseEnd_84705 := by
    simpa [prefixWord, tailWord_84705, baseEnd_84705] using wordTrace_append hprefix tailTrace_84705
  have hstable : (prefixWord ++ tailWord_84705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84705).length < 2 ^ (prefixWord ++ tailWord_84705).sum := by decide
  have hdescent : baseEnd_84705 < baseStart_84705 := by decide
  rcases family_descends (prefixWord ++ tailWord_84705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84707 : List Nat := [1, 1, 1, 7, 1, 1, 1, 1, 4, 4]
def baseStart_84707 : Nat := 118140960795 + 84707 * 2 ^ 59
def prefixEnd_84707 : Nat := 4983230072969 + 3 ^ 40 * 84707 * 2
def baseEnd_84707 : Nat := 28996937200336878115297

theorem tailTrace_84707 : CollatzResearch.WordTrace tailWord_84707 prefixEnd_84707 28996937200336878115297 := by
  unfold tailWord_84707
  simp only [CollatzResearch.WordTrace]
  refine ⟨3089518104128480648948375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2059678736085653765965583 3089518104128480648948375)
  ·
    refine ⟨4634277156192720973422563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3089518104128480648948375 4634277156192720973422563)
    ·
      refine ⟨6951415734289081460133845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4634277156192720973422563 6951415734289081460133845)
      ·
        refine ⟨162923806272400346721887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 6951415734289081460133845 162923806272400346721887)
        ·
          refine ⟨244385709408600520082831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162923806272400346721887 244385709408600520082831)
          ·
            refine ⟨366578564112900780124247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244385709408600520082831 366578564112900780124247)
            ·
              refine ⟨549867846169351170186371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366578564112900780124247 549867846169351170186371)
              ·
                refine ⟨824801769254026755279557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 549867846169351170186371 824801769254026755279557)
                ·
                  refine ⟨154650331735130016614917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 824801769254026755279557 154650331735130016614917)
                  ·
                    refine ⟨28996937200336878115297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 154650331735130016614917 28996937200336878115297)
                    ·
                      rfl

theorem cell22_84707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 4].length) (baseStart_84707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_84707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_84707 prefixEnd_84707 := by exact prefixLift 84707
  have htrace : WordTrace (prefixWord ++ tailWord_84707) baseStart_84707 baseEnd_84707 := by
    simpa [prefixWord, tailWord_84707, baseEnd_84707] using wordTrace_append hprefix tailTrace_84707
  have hstable : (prefixWord ++ tailWord_84707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84707).length < 2 ^ (prefixWord ++ tailWord_84707).sum := by decide
  have hdescent : baseEnd_84707 < baseStart_84707 := by decide
  rcases family_descends (prefixWord ++ tailWord_84707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84722 : List Nat := [3, 2, 1, 3, 1, 3, 2, 7]
def baseStart_84722 : Nat := 118140960795 + 84722 * 2 ^ 59
def prefixEnd_84722 : Nat := 4983230072969 + 3 ^ 40 * 84722 * 2
def baseEnd_84722 : Nat := 3222452445209093221139

theorem tailTrace_84722 : CollatzResearch.WordTrace tailWord_84722 prefixEnd_84722 3222452445209093221139 := by
  unfold tailWord_84722
  simp only [CollatzResearch.WordTrace]
  refine ⟨772516299768534552686105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2060043466049425473829613 772516299768534552686105)
  ·
    refine ⟨579387224826400914514579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 772516299768534552686105 579387224826400914514579)
    ·
      refine ⟨869080837239601371771869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 579387224826400914514579 869080837239601371771869)
      ·
        refine ⟨325905313964850514414451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 869080837239601371771869 325905313964850514414451)
        ·
          refine ⟨488857970947275771621677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325905313964850514414451 488857970947275771621677)
          ·
            refine ⟨183321739105228414358129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 488857970947275771621677 183321739105228414358129)
            ·
              refine ⟨137491304328921310768597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183321739105228414358129 137491304328921310768597)
              ·
                refine ⟨3222452445209093221139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 137491304328921310768597 3222452445209093221139)
                ·
                  rfl

theorem cell22_84722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 7].length) (baseStart_84722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_84722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_84722 prefixEnd_84722 := by exact prefixLift 84722
  have htrace : WordTrace (prefixWord ++ tailWord_84722) baseStart_84722 baseEnd_84722 := by
    simpa [prefixWord, tailWord_84722, baseEnd_84722] using wordTrace_append hprefix tailTrace_84722
  have hstable : (prefixWord ++ tailWord_84722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84722).length < 2 ^ (prefixWord ++ tailWord_84722).sum := by decide
  have hdescent : baseEnd_84722 < baseStart_84722 := by decide
  rcases family_descends (prefixWord ++ tailWord_84722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84737 : List Nat := [1, 2, 4, 1, 1, 1, 1, 3, 5, 3]
def baseStart_84737 : Nat := 118140960795 + 84737 * 2 ^ 59
def prefixEnd_84737 : Nat := 4983230072969 + 3 ^ 40 * 84737 * 2
def baseEnd_84737 : Nat := 29007206813426799865205

theorem tailTrace_84737 : CollatzResearch.WordTrace tailWord_84737 prefixEnd_84737 29007206813426799865205 := by
  unfold tailWord_84737
  simp only [CollatzResearch.WordTrace]
  refine ⟨3090612294019795772540465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2060408196013197181693643 3090612294019795772540465)
  ·
    refine ⟨2317959220514846829405349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3090612294019795772540465 2317959220514846829405349)
    ·
      refine ⟨434617353846533780513503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2317959220514846829405349 434617353846533780513503)
      ·
        refine ⟨651926030769800670770255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434617353846533780513503 651926030769800670770255)
        ·
          refine ⟨977889046154701006155383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 651926030769800670770255 977889046154701006155383)
          ·
            refine ⟨1466833569232051509233075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 977889046154701006155383 1466833569232051509233075)
            ·
              refine ⟨2200250353848077263849613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1466833569232051509233075 2200250353848077263849613)
              ·
                refine ⟨825093882693028973943605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2200250353848077263849613 825093882693028973943605)
                ·
                  refine ⟨77352551502471466307213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 825093882693028973943605 77352551502471466307213)
                  ·
                    refine ⟨29007206813426799865205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77352551502471466307213 29007206813426799865205)
                    ·
                      rfl

theorem cell22_84737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_84737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_84737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_84737 prefixEnd_84737 := by exact prefixLift 84737
  have htrace : WordTrace (prefixWord ++ tailWord_84737) baseStart_84737 baseEnd_84737 := by
    simpa [prefixWord, tailWord_84737, baseEnd_84737] using wordTrace_append hprefix tailTrace_84737
  have hstable : (prefixWord ++ tailWord_84737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84737).length < 2 ^ (prefixWord ++ tailWord_84737).sum := by decide
  have hdescent : baseEnd_84737 < baseStart_84737 := by decide
  rcases family_descends (prefixWord ++ tailWord_84737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84767 : List Nat := [1, 1, 2, 4, 2, 2, 1, 4, 5]
def baseStart_84767 : Nat := 118140960795 + 84767 * 2 ^ 59
def prefixEnd_84767 : Nat := 4983230072969 + 3 ^ 40 * 84767 * 2
def baseEnd_84767 : Nat := 9672492142172240538371

theorem tailTrace_84767 : CollatzResearch.WordTrace tailWord_84767 prefixEnd_84767 9672492142172240538371 := by
  unfold tailWord_84767
  simp only [CollatzResearch.WordTrace]
  refine ⟨3091706483911110896132555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2061137655940740597421703 3091706483911110896132555)
  ·
    refine ⟨4637559725866666344198833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3091706483911110896132555 4637559725866666344198833)
    ·
      refine ⟨3478169794399999758149125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4637559725866666344198833 3478169794399999758149125)
      ·
        refine ⟨652156836449999954652961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3478169794399999758149125 652156836449999954652961)
        ·
          refine ⟨489117627337499965989721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 652156836449999954652961 489117627337499965989721)
          ·
            refine ⟨366838220503124974492291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 489117627337499965989721 366838220503124974492291)
            ·
              refine ⟨550257330754687461738437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366838220503124974492291 550257330754687461738437)
              ·
                refine ⟨103173249516503899075957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 550257330754687461738437 103173249516503899075957)
                ·
                  refine ⟨9672492142172240538371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103173249516503899075957 9672492142172240538371)
                  ·
                    rfl

theorem cell22_84767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 5].length) (baseStart_84767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_84767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_84767 prefixEnd_84767 := by exact prefixLift 84767
  have htrace : WordTrace (prefixWord ++ tailWord_84767) baseStart_84767 baseEnd_84767 := by
    simpa [prefixWord, tailWord_84767, baseEnd_84767] using wordTrace_append hprefix tailTrace_84767
  have hstable : (prefixWord ++ tailWord_84767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84767).length < 2 ^ (prefixWord ++ tailWord_84767).sum := by decide
  have hdescent : baseEnd_84767 < baseStart_84767 := by decide
  rcases family_descends (prefixWord ++ tailWord_84767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84857 : List Nat := [1, 2, 1, 3, 2, 4, 1, 8]
def baseStart_84857 : Nat := 118140960795 + 84857 * 2 ^ 59
def prefixEnd_84857 : Nat := 4983230072969 + 3 ^ 40 * 84857 * 2
def baseEnd_84857 : Nat := 3227587251754054096093

theorem tailTrace_84857 : CollatzResearch.WordTrace tailWord_84857 prefixEnd_84857 3227587251754054096093 := by
  unfold tailWord_84857
  simp only [CollatzResearch.WordTrace]
  refine ⟨3094989053585056266908825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2063326035723370844605883 3094989053585056266908825)
  ·
    refine ⟨2321241790188792200181619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3094989053585056266908825 2321241790188792200181619)
    ·
      refine ⟨3481862685283188300272429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2321241790188792200181619 3481862685283188300272429)
      ·
        refine ⟨1305698506981195612602161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3481862685283188300272429 1305698506981195612602161)
        ·
          refine ⟨979273880235896709451621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1305698506981195612602161 979273880235896709451621)
          ·
            refine ⟨183613852544230633022179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 979273880235896709451621 183613852544230633022179)
            ·
              refine ⟨275420778816345949533269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183613852544230633022179 275420778816345949533269)
              ·
                refine ⟨3227587251754054096093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 275420778816345949533269 3227587251754054096093)
                ·
                  rfl

theorem cell22_84857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 8].length) (baseStart_84857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_84857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_84857 prefixEnd_84857 := by exact prefixLift 84857
  have htrace : WordTrace (prefixWord ++ tailWord_84857) baseStart_84857 baseEnd_84857 := by
    simpa [prefixWord, tailWord_84857, baseEnd_84857] using wordTrace_append hprefix tailTrace_84857
  have hstable : (prefixWord ++ tailWord_84857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84857).length < 2 ^ (prefixWord ++ tailWord_84857).sum := by decide
  have hdescent : baseEnd_84857 < baseStart_84857 := by decide
  rcases family_descends (prefixWord ++ tailWord_84857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84874 : List Nat := [3, 1, 2, 4, 1, 3, 8]
def baseStart_84874 : Nat := 118140960795 + 84874 * 2 ^ 59
def prefixEnd_84874 : Nat := 4983230072969 + 3 ^ 40 * 84874 * 2
def baseEnd_84874 : Nat := 1076077952340892932955

theorem tailTrace_84874 : CollatzResearch.WordTrace tailWord_84874 prefixEnd_84874 1076077952340892932955 := by
  unfold tailWord_84874
  simp only [CollatzResearch.WordTrace]
  refine ⟨773902273630867042569419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2063739396348978780185117 773902273630867042569419)
  ·
    refine ⟨1160853410446300563854129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 773902273630867042569419 1160853410446300563854129)
    ·
      refine ⟨870640057834725422890597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1160853410446300563854129 870640057834725422890597)
      ·
        refine ⟨163245010844011016791987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 870640057834725422890597 163245010844011016791987)
        ·
          refine ⟨244867516266016525187981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163245010844011016791987 244867516266016525187981)
          ·
            refine ⟨91825318599756196945493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 244867516266016525187981 91825318599756196945493)
            ·
              refine ⟨1076077952340892932955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 91825318599756196945493 1076077952340892932955)
              ·
                rfl

theorem cell22_84874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 8].length) (baseStart_84874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_84874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_84874 prefixEnd_84874 := by exact prefixLift 84874
  have htrace : WordTrace (prefixWord ++ tailWord_84874) baseStart_84874 baseEnd_84874 := by
    simpa [prefixWord, tailWord_84874, baseEnd_84874] using wordTrace_append hprefix tailTrace_84874
  have hstable : (prefixWord ++ tailWord_84874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84874).length < 2 ^ (prefixWord ++ tailWord_84874).sum := by decide
  have hdescent : baseEnd_84874 < baseStart_84874 := by decide
  rcases family_descends (prefixWord ++ tailWord_84874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84887 : List Nat := [1, 1, 3, 3, 1, 2, 2, 1, 2, 6]
def baseStart_84887 : Nat := 118140960795 + 84887 * 2 ^ 59
def prefixEnd_84887 : Nat := 4983230072969 + 3 ^ 40 * 84887 * 2
def baseEnd_84887 : Nat := 29058554878876408614745

theorem tailTrace_84887 : CollatzResearch.WordTrace tailWord_84887 prefixEnd_84887 29058554878876408614745 := by
  unfold tailWord_84887
  simp only [CollatzResearch.WordTrace]
  refine ⟨3096083243476371390500915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2064055495650914260333943 3096083243476371390500915)
  ·
    refine ⟨4644124865214557085751373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3096083243476371390500915 4644124865214557085751373)
    ·
      refine ⟨1741546824455458907156765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4644124865214557085751373 1741546824455458907156765)
      ·
        refine ⟨653080059170797090183787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1741546824455458907156765 653080059170797090183787)
        ·
          refine ⟨979620088756195635275681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 653080059170797090183787 979620088756195635275681)
          ·
            refine ⟨734715066567146726456761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 979620088756195635275681 734715066567146726456761)
            ·
              refine ⟨551036299925360044842571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 734715066567146726456761 551036299925360044842571)
              ·
                refine ⟨826554449888040067263857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 551036299925360044842571 826554449888040067263857)
                ·
                  refine ⟨619915837416030050447893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 826554449888040067263857 619915837416030050447893)
                  ·
                    refine ⟨29058554878876408614745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 619915837416030050447893 29058554878876408614745)
                    ·
                      rfl

theorem cell22_84887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_84887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_84887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_84887 prefixEnd_84887 := by exact prefixLift 84887
  have htrace : WordTrace (prefixWord ++ tailWord_84887) baseStart_84887 baseEnd_84887 := by
    simpa [prefixWord, tailWord_84887, baseEnd_84887] using wordTrace_append hprefix tailTrace_84887
  have hstable : (prefixWord ++ tailWord_84887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84887).length < 2 ^ (prefixWord ++ tailWord_84887).sum := by decide
  have hdescent : baseEnd_84887 < baseStart_84887 := by decide
  rcases family_descends (prefixWord ++ tailWord_84887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84936 : List Nat := [2, 1, 3, 1, 5, 1, 2, 2, 5]
def baseStart_84936 : Nat := 118140960795 + 84936 * 2 ^ 59
def prefixEnd_84936 : Nat := 4983230072969 + 3 ^ 40 * 84936 * 2
def baseEnd_84936 : Nat := 9691776193418871379865

theorem tailTrace_84936 : CollatzResearch.WordTrace tailWord_84936 prefixEnd_84936 9691776193418871379865 := by
  unfold tailWord_84936
  simp only [CollatzResearch.WordTrace]
  refine ⟨1548935210149426379517331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2065246946865901839356441 1548935210149426379517331)
  ·
    refine ⟨2323402815224139569275997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1548935210149426379517331 2323402815224139569275997)
    ·
      refine ⟨871276055709052338478499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2323402815224139569275997 871276055709052338478499)
      ·
        refine ⟨1306914083563578507717749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 871276055709052338478499 1306914083563578507717749)
        ·
          refine ⟨122523195334085485098539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1306914083563578507717749 122523195334085485098539)
          ·
            refine ⟨183784793001128227647809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122523195334085485098539 183784793001128227647809)
            ·
              refine ⟨137838594750846170735857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183784793001128227647809 137838594750846170735857)
              ·
                refine ⟨103378946063134628051893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137838594750846170735857 103378946063134628051893)
                ·
                  refine ⟨9691776193418871379865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103378946063134628051893 9691776193418871379865)
                  ·
                    rfl

theorem cell22_84936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 5].length) (baseStart_84936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_84936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_84936 prefixEnd_84936 := by exact prefixLift 84936
  have htrace : WordTrace (prefixWord ++ tailWord_84936) baseStart_84936 baseEnd_84936 := by
    simpa [prefixWord, tailWord_84936, baseEnd_84936] using wordTrace_append hprefix tailTrace_84936
  have hstable : (prefixWord ++ tailWord_84936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84936).length < 2 ^ (prefixWord ++ tailWord_84936).sum := by decide
  have hdescent : baseEnd_84936 < baseStart_84936 := by decide
  rcases family_descends (prefixWord ++ tailWord_84936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85026 : List Nat := [3, 3, 1, 1, 1, 3, 4, 6]
def baseStart_85026 : Nat := 118140960795 + 85026 * 2 ^ 59
def prefixEnd_85026 : Nat := 4983230072969 + 3 ^ 40 * 85026 * 2
def baseEnd_85026 : Nat := 3234015268836264376591

theorem tailTrace_85026 : CollatzResearch.WordTrace tailWord_85026 prefixEnd_85026 3234015268836264376591 := by
  unfold tailWord_85026
  simp only [CollatzResearch.WordTrace]
  refine ⟨775288247493199532452733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2067435326648532086540621 775288247493199532452733)
  ·
    refine ⟨290733092809949824669775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 775288247493199532452733 290733092809949824669775)
    ·
      refine ⟨436099639214924737004663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290733092809949824669775 436099639214924737004663)
      ·
        refine ⟨654149458822387105506995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436099639214924737004663 654149458822387105506995)
        ·
          refine ⟨981224188233580658260493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 654149458822387105506995 981224188233580658260493)
          ·
            refine ⟨367959070587592746847685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 981224188233580658260493 367959070587592746847685)
            ·
              refine ⟨68992325735173640033941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 367959070587592746847685 68992325735173640033941)
              ·
                refine ⟨3234015268836264376591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68992325735173640033941 3234015268836264376591)
                ·
                  rfl

theorem cell22_85026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 6].length) (baseStart_85026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_85026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_85026 prefixEnd_85026 := by exact prefixLift 85026
  have htrace : WordTrace (prefixWord ++ tailWord_85026) baseStart_85026 baseEnd_85026 := by
    simpa [prefixWord, tailWord_85026, baseEnd_85026] using wordTrace_append hprefix tailTrace_85026
  have hstable : (prefixWord ++ tailWord_85026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85026).length < 2 ^ (prefixWord ++ tailWord_85026).sum := by decide
  have hdescent : baseEnd_85026 < baseStart_85026 := by decide
  rcases family_descends (prefixWord ++ tailWord_85026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85150 : List Nat := [4, 3, 1, 1, 2, 1, 1, 5, 4]
def baseStart_85150 : Nat := 118140960795 + 85150 * 2 ^ 59
def prefixEnd_85150 : Nat := 4983230072969 + 3 ^ 40 * 85150 * 2
def baseEnd_85150 : Nat := 9716195051210463096313

theorem tailTrace_85150 : CollatzResearch.WordTrace tailWord_85150 prefixEnd_85150 9716195051210463096313 := by
  unfold tailWord_85150
  simp only [CollatzResearch.WordTrace]
  refine ⟨388209455190445913415613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2070450427682378204883269 388209455190445913415613)
  ·
    refine ⟨145578545696417217530855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 388209455190445913415613 145578545696417217530855)
    ·
      refine ⟨218367818544625826296283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145578545696417217530855 218367818544625826296283)
      ·
        refine ⟨327551727816938739444425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218367818544625826296283 327551727816938739444425)
        ·
          refine ⟨245663795862704054583319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 327551727816938739444425 245663795862704054583319)
          ·
            refine ⟨368495693794056081874979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245663795862704054583319 368495693794056081874979)
            ·
              refine ⟨552743540691084122812469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 368495693794056081874979 552743540691084122812469)
              ·
                refine ⟨51819706939789136513669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 552743540691084122812469 51819706939789136513669)
                ·
                  refine ⟨9716195051210463096313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51819706939789136513669 9716195051210463096313)
                  ·
                    rfl

theorem cell22_85150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_85150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_85150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_85150 prefixEnd_85150 := by exact prefixLift 85150
  have htrace : WordTrace (prefixWord ++ tailWord_85150) baseStart_85150 baseEnd_85150 := by
    simpa [prefixWord, tailWord_85150, baseEnd_85150] using wordTrace_append hprefix tailTrace_85150
  have hstable : (prefixWord ++ tailWord_85150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85150).length < 2 ^ (prefixWord ++ tailWord_85150).sum := by decide
  have hdescent : baseEnd_85150 < baseStart_85150 := by decide
  rcases family_descends (prefixWord ++ tailWord_85150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85165 : List Nat := [1, 5, 2, 1, 3, 1, 1, 1, 4, 3]
def baseStart_85165 : Nat := 118140960795 + 85165 * 2 ^ 59
def prefixEnd_85165 : Nat := 4983230072969 + 3 ^ 40 * 85165 * 2
def baseEnd_85165 : Nat := 29153719960176350163893

theorem tailTrace_85165 : CollatzResearch.WordTrace tailWord_85165 prefixEnd_85165 29153719960176350163893 := by
  unfold tailWord_85165
  simp only [CollatzResearch.WordTrace]
  refine ⟨3106222736469224869120949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2070815157646149912747299 3106222736469224869120949)
  ·
    refine ⟨291208381543989831480089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3106222736469224869120949 291208381543989831480089)
    ·
      refine ⟨218406286157992373610067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291208381543989831480089 218406286157992373610067)
      ·
        refine ⟨327609429236988560415101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218406286157992373610067 327609429236988560415101)
        ·
          refine ⟨122853535963870710155663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 327609429236988560415101 122853535963870710155663)
          ·
            refine ⟨184280303945806065233495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122853535963870710155663 184280303945806065233495)
            ·
              refine ⟨276420455918709097850243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184280303945806065233495 276420455918709097850243)
              ·
                refine ⟨414630683878063646775365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 276420455918709097850243 414630683878063646775365)
                ·
                  refine ⟨77743253227136933770381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 414630683878063646775365 77743253227136933770381)
                  ·
                    refine ⟨29153719960176350163893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77743253227136933770381 29153719960176350163893)
                    ·
                      rfl

theorem cell22_85165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_85165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_85165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_85165 prefixEnd_85165 := by exact prefixLift 85165
  have htrace : WordTrace (prefixWord ++ tailWord_85165) baseStart_85165 baseEnd_85165 := by
    simpa [prefixWord, tailWord_85165, baseEnd_85165] using wordTrace_append hprefix tailTrace_85165
  have hstable : (prefixWord ++ tailWord_85165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85165).length < 2 ^ (prefixWord ++ tailWord_85165).sum := by decide
  have hdescent : baseEnd_85165 < baseStart_85165 := by decide
  rcases family_descends (prefixWord ++ tailWord_85165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85182 : List Nat := [4, 2, 1, 1, 3, 2, 3, 1, 2, 3]
def baseStart_85182 : Nat := 118140960795 + 85182 * 2 ^ 59
def prefixEnd_85182 : Nat := 4983230072969 + 3 ^ 40 * 85182 * 2
def baseEnd_85182 : Nat := 29159539407593972488841

theorem tailTrace_85182 : CollatzResearch.WordTrace tailWord_85182 prefixEnd_85182 29159539407593972488841 := by
  unfold tailWord_85182
  simp only [CollatzResearch.WordTrace]
  refine ⟨388355347175954596561225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2071228518271757848326533 388355347175954596561225)
  ·
    refine ⟨291266510381965947420919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 388355347175954596561225 291266510381965947420919)
    ·
      refine ⟨436899765572948921131379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 291266510381965947420919 436899765572948921131379)
      ·
        refine ⟨655349648359423381697069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436899765572948921131379 655349648359423381697069)
        ·
          refine ⟨245756118134783768136401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 655349648359423381697069 245756118134783768136401)
          ·
            refine ⟨184317088601087826102301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245756118134783768136401 184317088601087826102301)
            ·
              refine ⟨69118908225407934788363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184317088601087826102301 69118908225407934788363)
              ·
                refine ⟨103678362338111902182545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69118908225407934788363 103678362338111902182545)
                ·
                  refine ⟨77758771753583926636909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103678362338111902182545 77758771753583926636909)
                  ·
                    refine ⟨29159539407593972488841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77758771753583926636909 29159539407593972488841)
                    ·
                      rfl

theorem cell22_85182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_85182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_85182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_85182 prefixEnd_85182 := by exact prefixLift 85182
  have htrace : WordTrace (prefixWord ++ tailWord_85182) baseStart_85182 baseEnd_85182 := by
    simpa [prefixWord, tailWord_85182, baseEnd_85182] using wordTrace_append hprefix tailTrace_85182
  have hstable : (prefixWord ++ tailWord_85182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85182).length < 2 ^ (prefixWord ++ tailWord_85182).sum := by decide
  have hdescent : baseEnd_85182 < baseStart_85182 := by decide
  rcases family_descends (prefixWord ++ tailWord_85182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85227 : List Nat := [1, 1, 1, 1, 2, 7, 3, 2, 1, 3]
def baseStart_85227 : Nat := 118140960795 + 85227 * 2 ^ 59
def prefixEnd_85227 : Nat := 4983230072969 + 3 ^ 40 * 85227 * 2
def baseEnd_85227 : Nat := 29174943827228855113703

theorem tailTrace_85227 : CollatzResearch.WordTrace tailWord_85227 prefixEnd_85227 29174943827228855113703 := by
  unfold tailWord_85227
  simp only [CollatzResearch.WordTrace]
  refine ⟨3108484062244609457877935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2072322708163072971918623 3108484062244609457877935)
  ·
    refine ⟨4662726093366914186816903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3108484062244609457877935 4662726093366914186816903)
    ·
      refine ⟨6994089140050371280225355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4662726093366914186816903 6994089140050371280225355)
      ·
        refine ⟨10491133710075556920338033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6994089140050371280225355 10491133710075556920338033)
        ·
          refine ⟨7868350282556667690253525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10491133710075556920338033 7868350282556667690253525)
          ·
            refine ⟨184414459747421898990317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 7868350282556667690253525 184414459747421898990317)
            ·
              refine ⟨69155422405283212121369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184414459747421898990317 69155422405283212121369)
              ·
                refine ⟨51866566803962409091027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69155422405283212121369 51866566803962409091027)
                ·
                  refine ⟨77799850205943613636541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51866566803962409091027 77799850205943613636541)
                  ·
                    refine ⟨29174943827228855113703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77799850205943613636541 29174943827228855113703)
                    ·
                      rfl

theorem cell22_85227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 2, 1, 3].length) (baseStart_85227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_85227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_85227 prefixEnd_85227 := by exact prefixLift 85227
  have htrace : WordTrace (prefixWord ++ tailWord_85227) baseStart_85227 baseEnd_85227 := by
    simpa [prefixWord, tailWord_85227, baseEnd_85227] using wordTrace_append hprefix tailTrace_85227
  have hstable : (prefixWord ++ tailWord_85227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85227).length < 2 ^ (prefixWord ++ tailWord_85227).sum := by decide
  have hdescent : baseEnd_85227 < baseStart_85227 := by decide
  rcases family_descends (prefixWord ++ tailWord_85227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85278 : List Nat := [4, 3, 2, 1, 2, 2, 2, 2, 1, 3]
def baseStart_85278 : Nat := 118140960795 + 85278 * 2 ^ 59
def prefixEnd_85278 : Nat := 4983230072969 + 3 ^ 40 * 85278 * 2
def baseEnd_85278 : Nat := 29192402169481722088547

theorem tailTrace_85278 : CollatzResearch.WordTrace tailWord_85278 prefixEnd_85278 29192402169481722088547 := by
  unfold tailWord_85278
  simp only [CollatzResearch.WordTrace]
  refine ⟨388793023132480645998061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2073562790039896778656325 388793023132480645998061)
  ·
    refine ⟨145797383674680242249273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 388793023132480645998061 145797383674680242249273)
    ·
      refine ⟨109348037756010181686955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145797383674680242249273 109348037756010181686955)
      ·
        refine ⟨164022056634015272530433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109348037756010181686955 164022056634015272530433)
        ·
          refine ⟨123016542475511454397825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164022056634015272530433 123016542475511454397825)
          ·
            refine ⟨92262406856633590798369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123016542475511454397825 92262406856633590798369)
            ·
              refine ⟨69196805142475193098777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92262406856633590798369 69196805142475193098777)
              ·
                refine ⟨51897603856856394824083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69196805142475193098777 51897603856856394824083)
                ·
                  refine ⟨77846405785284592236125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51897603856856394824083 77846405785284592236125)
                  ·
                    refine ⟨29192402169481722088547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77846405785284592236125 29192402169481722088547)
                    ·
                      rfl

theorem cell22_85278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_85278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_85278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_85278 prefixEnd_85278 := by exact prefixLift 85278
  have htrace : WordTrace (prefixWord ++ tailWord_85278) baseStart_85278 baseEnd_85278 := by
    simpa [prefixWord, tailWord_85278, baseEnd_85278] using wordTrace_append hprefix tailTrace_85278
  have hstable : (prefixWord ++ tailWord_85278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85278).length < 2 ^ (prefixWord ++ tailWord_85278).sum := by decide
  have hdescent : baseEnd_85278 < baseStart_85278 := by decide
  rcases family_descends (prefixWord ++ tailWord_85278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85281 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 3, 6]
def baseStart_85281 : Nat := 118140960795 + 85281 * 2 ^ 59
def prefixEnd_85281 : Nat := 4983230072969 + 3 ^ 40 * 85281 * 2
def baseEnd_85281 : Nat := 29193429130790714263537

theorem tailTrace_85281 : CollatzResearch.WordTrace tailWord_85281 prefixEnd_85281 29193429130790714263537 := by
  unfold tailWord_85281
  simp only [CollatzResearch.WordTrace]
  refine ⟨3110453604048976680343697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2073635736032651120229131 3110453604048976680343697)
  ·
    refine ⟨2332840203036732510257773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3110453604048976680343697 2332840203036732510257773)
    ·
      refine ⟨874815076138774691346665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2332840203036732510257773 874815076138774691346665)
      ·
        refine ⟨656111307104081018509999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 874815076138774691346665 656111307104081018509999)
        ·
          refine ⟨984166960656121527764999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 656111307104081018509999 984166960656121527764999)
          ·
            refine ⟨1476250440984182291647499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 984166960656121527764999 1476250440984182291647499)
            ·
              refine ⟨2214375661476273437471249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1476250440984182291647499 2214375661476273437471249)
              ·
                refine ⟨1660781746107205078103437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2214375661476273437471249 1660781746107205078103437)
                ·
                  refine ⟨622793154790201904288789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1660781746107205078103437 622793154790201904288789)
                  ·
                    refine ⟨29193429130790714263537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 622793154790201904288789 29193429130790714263537)
                    ·
                      rfl

theorem cell22_85281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_85281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_85281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_85281 prefixEnd_85281 := by exact prefixLift 85281
  have htrace : WordTrace (prefixWord ++ tailWord_85281) baseStart_85281 baseEnd_85281 := by
    simpa [prefixWord, tailWord_85281, baseEnd_85281] using wordTrace_append hprefix tailTrace_85281
  have hstable : (prefixWord ++ tailWord_85281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85281).length < 2 ^ (prefixWord ++ tailWord_85281).sum := by decide
  have hdescent : baseEnd_85281 < baseStart_85281 := by decide
  rcases family_descends (prefixWord ++ tailWord_85281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85285 : List Nat := [1, 3, 1, 2, 4, 2, 1, 4, 4]
def baseStart_85285 : Nat := 118140960795 + 85285 * 2 ^ 59
def prefixEnd_85285 : Nat := 4983230072969 + 3 ^ 40 * 85285 * 2
def baseEnd_85285 : Nat := 9731599470845345721175

theorem tailTrace_85285 : CollatzResearch.WordTrace tailWord_85285 prefixEnd_85285 9731599470845345721175 := by
  unfold tailWord_85285
  simp only [CollatzResearch.WordTrace]
  refine ⟨3110599496034485363489309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2073732997356323575659539 3110599496034485363489309)
  ·
    refine ⟨1166474811012932011308491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3110599496034485363489309 1166474811012932011308491)
    ·
      refine ⟨1749712216519398016962737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1166474811012932011308491 1749712216519398016962737)
      ·
        refine ⟨1312284162389548512722053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1749712216519398016962737 1312284162389548512722053)
        ·
          refine ⟨246053280448040346135385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1312284162389548512722053 246053280448040346135385)
          ·
            refine ⟨184539960336030259601539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246053280448040346135385 184539960336030259601539)
            ·
              refine ⟨276809940504045389402309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184539960336030259601539 276809940504045389402309)
              ·
                refine ⟨51901863844508510512933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 276809940504045389402309 51901863844508510512933)
                ·
                  refine ⟨9731599470845345721175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51901863844508510512933 9731599470845345721175)
                  ·
                    rfl

theorem cell22_85285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 4, 4].length) (baseStart_85285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_85285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_85285 prefixEnd_85285 := by exact prefixLift 85285
  have htrace : WordTrace (prefixWord ++ tailWord_85285) baseStart_85285 baseEnd_85285 := by
    simpa [prefixWord, tailWord_85285, baseEnd_85285] using wordTrace_append hprefix tailTrace_85285
  have hstable : (prefixWord ++ tailWord_85285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85285).length < 2 ^ (prefixWord ++ tailWord_85285).sum := by decide
  have hdescent : baseEnd_85285 < baseStart_85285 := by decide
  rcases family_descends (prefixWord ++ tailWord_85285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85300 : List Nat := [2, 5, 1, 1, 1, 1, 4, 1, 1, 5]
def baseStart_85300 : Nat := 118140960795 + 85300 * 2 ^ 59
def prefixEnd_85300 : Nat := 4983230072969 + 3 ^ 40 * 85300 * 2
def baseEnd_85300 : Nat := 29199933219080998038479

theorem tailTrace_85300 : CollatzResearch.WordTrace tailWord_85300 prefixEnd_85300 29199933219080998038479 := by
  unfold tailWord_85300
  simp only [CollatzResearch.WordTrace]
  refine ⟨1555573295490071462642677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2074097727320095283523569 1555573295490071462642677)
  ·
    refine ⟨145834996452194199622751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1555573295490071462642677 145834996452194199622751)
    ·
      refine ⟨218752494678291299434127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145834996452194199622751 218752494678291299434127)
      ·
        refine ⟨328128742017436949151191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218752494678291299434127 328128742017436949151191)
        ·
          refine ⟨492193113026155423726787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328128742017436949151191 492193113026155423726787)
          ·
            refine ⟨738289669539233135590181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 492193113026155423726787 738289669539233135590181)
            ·
              refine ⟨138429313038606212923159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 738289669539233135590181 138429313038606212923159)
              ·
                refine ⟨207643969557909319384739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138429313038606212923159 207643969557909319384739)
                ·
                  refine ⟨311465954336863979077109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 207643969557909319384739 311465954336863979077109)
                  ·
                    refine ⟨29199933219080998038479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 311465954336863979077109 29199933219080998038479)
                    ·
                      rfl

theorem cell22_85300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_85300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_85300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_85300 prefixEnd_85300 := by exact prefixLift 85300
  have htrace : WordTrace (prefixWord ++ tailWord_85300) baseStart_85300 baseEnd_85300 := by
    simpa [prefixWord, tailWord_85300, baseEnd_85300] using wordTrace_append hprefix tailTrace_85300
  have hstable : (prefixWord ++ tailWord_85300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85300).length < 2 ^ (prefixWord ++ tailWord_85300).sum := by decide
  have hdescent : baseEnd_85300 < baseStart_85300 := by decide
  rcases family_descends (prefixWord ++ tailWord_85300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85302 : List Nat := [5, 1, 2, 3, 1, 1, 1, 2, 6]
def baseStart_85302 : Nat := 118140960795 + 85302 * 2 ^ 59
def prefixEnd_85302 : Nat := 4983230072969 + 3 ^ 40 * 85302 * 2
def baseEnd_85302 : Nat := 9733539286651219829491

theorem tailTrace_85302 : CollatzResearch.WordTrace tailWord_85302 prefixEnd_85302 9733539286651219829491 := by
  unfold tailWord_85302
  simp only [CollatzResearch.WordTrace]
  refine ⟨194451221060806079178635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2074146357981931511238773 194451221060806079178635)
  ·
    refine ⟨291676831591209118767953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194451221060806079178635 291676831591209118767953)
    ·
      refine ⟨218757623693406839075965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291676831591209118767953 218757623693406839075965)
      ·
        refine ⟨82034108885027564653487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218757623693406839075965 82034108885027564653487)
        ·
          refine ⟨123051163327541346980231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82034108885027564653487 123051163327541346980231)
          ·
            refine ⟨184576744991312020470347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123051163327541346980231 184576744991312020470347)
            ·
              refine ⟨276865117486968030705521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184576744991312020470347 276865117486968030705521)
              ·
                refine ⟨207648838115226023029141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 276865117486968030705521 207648838115226023029141)
                ·
                  refine ⟨9733539286651219829491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 207648838115226023029141 9733539286651219829491)
                  ·
                    rfl

theorem cell22_85302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_85302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_85302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_85302 prefixEnd_85302 := by exact prefixLift 85302
  have htrace : WordTrace (prefixWord ++ tailWord_85302) baseStart_85302 baseEnd_85302 := by
    simpa [prefixWord, tailWord_85302, baseEnd_85302] using wordTrace_append hprefix tailTrace_85302
  have hstable : (prefixWord ++ tailWord_85302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85302).length < 2 ^ (prefixWord ++ tailWord_85302).sum := by decide
  have hdescent : baseEnd_85302 < baseStart_85302 := by decide
  rcases family_descends (prefixWord ++ tailWord_85302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85328 : List Nat := [2, 1, 1, 1, 1, 5, 1, 2, 5, 3]
def baseStart_85328 : Nat := 118140960795 + 85328 * 2 ^ 59
def prefixEnd_85328 : Nat := 4983230072969 + 3 ^ 40 * 85328 * 2
def baseEnd_85328 : Nat := 29209518191298258338393

theorem tailTrace_85328 : CollatzResearch.WordTrace tailWord_85328 prefixEnd_85328 29209518191298258338393 := by
  unfold tailWord_85328
  simp only [CollatzResearch.WordTrace]
  refine ⟨1556083917439351853652319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2074778556585802471536425 1556083917439351853652319)
  ·
    refine ⟨2334125876159027780478479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1556083917439351853652319 2334125876159027780478479)
    ·
      refine ⟨3501188814238541670717719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2334125876159027780478479 3501188814238541670717719)
      ·
        refine ⟨5251783221357812506076579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3501188814238541670717719 5251783221357812506076579)
        ·
          refine ⟨7877674832036718759114869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5251783221357812506076579 7877674832036718759114869)
          ·
            refine ⟨738532015503442383667019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7877674832036718759114869 738532015503442383667019)
            ·
              refine ⟨1107798023255163575500529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 738532015503442383667019 1107798023255163575500529)
              ·
                refine ⟨830848517441372681625397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1107798023255163575500529 830848517441372681625397)
                ·
                  refine ⟨77892048510128688902381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 830848517441372681625397 77892048510128688902381)
                  ·
                    refine ⟨29209518191298258338393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77892048510128688902381 29209518191298258338393)
                    ·
                      rfl

theorem cell22_85328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 5, 3].length) (baseStart_85328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_85328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_85328 prefixEnd_85328 := by exact prefixLift 85328
  have htrace : WordTrace (prefixWord ++ tailWord_85328) baseStart_85328 baseEnd_85328 := by
    simpa [prefixWord, tailWord_85328, baseEnd_85328] using wordTrace_append hprefix tailTrace_85328
  have hstable : (prefixWord ++ tailWord_85328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85328).length < 2 ^ (prefixWord ++ tailWord_85328).sum := by decide
  have hdescent : baseEnd_85328 < baseStart_85328 := by decide
  rcases family_descends (prefixWord ++ tailWord_85328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85379 : List Nat := [1, 1, 1, 3, 5, 3, 1, 3, 1, 3]
def baseStart_85379 : Nat := 118140960795 + 85379 * 2 ^ 59
def prefixEnd_85379 : Nat := 4983230072969 + 3 ^ 40 * 85379 * 2
def baseEnd_85379 : Nat := 29226976533551125313237

theorem tailTrace_85379 : CollatzResearch.WordTrace tailWord_85379 prefixEnd_85379 29226976533551125313237 := by
  unfold tailWord_85379
  simp only [CollatzResearch.WordTrace]
  refine ⟨3114027957693939417411191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2076018638462626278274127 3114027957693939417411191)
  ·
    refine ⟨4671041936540909126116787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3114027957693939417411191 4671041936540909126116787)
    ·
      refine ⟨7006562904811363689175181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4671041936540909126116787 7006562904811363689175181)
      ·
        refine ⟨2627461089304261383440693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7006562904811363689175181 2627461089304261383440693)
        ·
          refine ⟨246324477122274504697565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2627461089304261383440693 246324477122274504697565)
          ·
            refine ⟨92371678920852939261587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 246324477122274504697565 92371678920852939261587)
            ·
              refine ⟨138557518381279408892381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92371678920852939261587 138557518381279408892381)
              ·
                refine ⟨51959069392979778334643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138557518381279408892381 51959069392979778334643)
                ·
                  refine ⟨77938604089469667501965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51959069392979778334643 77938604089469667501965)
                  ·
                    refine ⟨29226976533551125313237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77938604089469667501965 29226976533551125313237)
                    ·
                      rfl

theorem cell22_85379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 3, 1, 3].length) (baseStart_85379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_85379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_85379 prefixEnd_85379 := by exact prefixLift 85379
  have htrace : WordTrace (prefixWord ++ tailWord_85379) baseStart_85379 baseEnd_85379 := by
    simpa [prefixWord, tailWord_85379, baseEnd_85379] using wordTrace_append hprefix tailTrace_85379
  have hstable : (prefixWord ++ tailWord_85379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85379).length < 2 ^ (prefixWord ++ tailWord_85379).sum := by decide
  have hdescent : baseEnd_85379 < baseStart_85379 := by decide
  rcases family_descends (prefixWord ++ tailWord_85379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85396 : List Nat := [2, 4, 2, 1, 2, 2, 3, 2, 1, 3]
def baseStart_85396 : Nat := 118140960795 + 85396 * 2 ^ 59
def prefixEnd_85396 : Nat := 4983230072969 + 3 ^ 40 * 85396 * 2
def baseEnd_85396 : Nat := 29232795980968747638185

theorem tailTrace_85396 : CollatzResearch.WordTrace tailWord_85396 prefixEnd_85396 29232795980968747638185 := by
  unfold tailWord_85396
  simp only [CollatzResearch.WordTrace]
  refine ⟨1557323999316175660390021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2076431999088234213853361 1557323999316175660390021)
  ·
    refine ⟨291998249871782936323129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1557323999316175660390021 291998249871782936323129)
    ·
      refine ⟨218998687403837202242347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 291998249871782936323129 218998687403837202242347)
      ·
        refine ⟨328498031105755803363521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218998687403837202242347 328498031105755803363521)
        ·
          refine ⟨246373523329316852522641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 328498031105755803363521 246373523329316852522641)
          ·
            refine ⟨184780142496987639391981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246373523329316852522641 184780142496987639391981)
            ·
              refine ⟨69292553436370364771993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184780142496987639391981 69292553436370364771993)
              ·
                refine ⟨51969415077277773578995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69292553436370364771993 51969415077277773578995)
                ·
                  refine ⟨77954122615916660368493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51969415077277773578995 77954122615916660368493)
                  ·
                    refine ⟨29232795980968747638185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77954122615916660368493 29232795980968747638185)
                    ·
                      rfl

theorem cell22_85396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_85396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_85396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_85396 prefixEnd_85396 := by exact prefixLift 85396
  have htrace : WordTrace (prefixWord ++ tailWord_85396) baseStart_85396 baseEnd_85396 := by
    simpa [prefixWord, tailWord_85396, baseEnd_85396] using wordTrace_append hprefix tailTrace_85396
  have hstable : (prefixWord ++ tailWord_85396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85396).length < 2 ^ (prefixWord ++ tailWord_85396).sum := by decide
  have hdescent : baseEnd_85396 < baseStart_85396 := by decide
  rcases family_descends (prefixWord ++ tailWord_85396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85450 : List Nat := [3, 1, 2, 1, 2, 3, 2, 2, 2, 4]
def baseStart_85450 : Nat := 118140960795 + 85450 * 2 ^ 59
def prefixEnd_85450 : Nat := 4983230072969 + 3 ^ 40 * 85450 * 2
def baseEnd_85450 : Nat := 29251281284530606788019

theorem tailTrace_85450 : CollatzResearch.WordTrace tailWord_85450 prefixEnd_85450 29251281284530606788019 := by
  unfold tailWord_85450
  simp only [CollatzResearch.WordTrace]
  refine ⟨779154385109179635811451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2077745026957812362163869 779154385109179635811451)
  ·
    refine ⟨1168731577663769453717177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 779154385109179635811451 1168731577663769453717177)
    ·
      refine ⟨876548683247827090287883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1168731577663769453717177 876548683247827090287883)
      ·
        refine ⟨1314823024871740635431825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 876548683247827090287883 1314823024871740635431825)
        ·
          refine ⟨986117268653805476573869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1314823024871740635431825 986117268653805476573869)
          ·
            refine ⟨369793975745177053715201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 986117268653805476573869 369793975745177053715201)
            ·
              refine ⟨277345481808882790286401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 369793975745177053715201 277345481808882790286401)
              ·
                refine ⟨208009111356662092714801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 277345481808882790286401 208009111356662092714801)
                ·
                  refine ⟨156006833517496569536101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 208009111356662092714801 156006833517496569536101)
                  ·
                    refine ⟨29251281284530606788019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 156006833517496569536101 29251281284530606788019)
                    ·
                      rfl

theorem cell22_85450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_85450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_85450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_85450 prefixEnd_85450 := by exact prefixLift 85450
  have htrace : WordTrace (prefixWord ++ tailWord_85450) baseStart_85450 baseEnd_85450 := by
    simpa [prefixWord, tailWord_85450, baseEnd_85450] using wordTrace_append hprefix tailTrace_85450
  have hstable : (prefixWord ++ tailWord_85450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85450).length < 2 ^ (prefixWord ++ tailWord_85450).sum := by decide
  have hdescent : baseEnd_85450 < baseStart_85450 := by decide
  rcases family_descends (prefixWord ++ tailWord_85450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85452 : List Nat := [2, 2, 1, 4, 2, 1, 1, 4, 2, 3]
def baseStart_85452 : Nat := 118140960795 + 85452 * 2 ^ 59
def prefixEnd_85452 : Nat := 4983230072969 + 3 ^ 40 * 85452 * 2
def baseEnd_85452 : Nat := 29251965925403268238013

theorem tailTrace_85452 : CollatzResearch.WordTrace tailWord_85452 prefixEnd_85452 29251965925403268238013 := by
  unfold tailWord_85452
  simp only [CollatzResearch.WordTrace]
  refine ⟨1558345243214736442409305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2077793657619648589879073 1558345243214736442409305)
  ·
    refine ⟨1168758932411052331806979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1558345243214736442409305 1168758932411052331806979)
    ·
      refine ⟨1753138398616578497710469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1168758932411052331806979 1753138398616578497710469)
      ·
        refine ⟨328713449740608468320713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1753138398616578497710469 328713449740608468320713)
        ·
          refine ⟨246535087305456351240535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 328713449740608468320713 246535087305456351240535)
          ·
            refine ⟨369802630958184526860803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246535087305456351240535 369802630958184526860803)
            ·
              refine ⟨554703946437276790291205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369802630958184526860803 554703946437276790291205)
              ·
                refine ⟨104006989956989398179601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 554703946437276790291205 104006989956989398179601)
                ·
                  refine ⟨78005242467742048634701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104006989956989398179601 78005242467742048634701)
                  ·
                    refine ⟨29251965925403268238013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78005242467742048634701 29251965925403268238013)
                    ·
                      rfl

theorem cell22_85452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 2, 3].length) (baseStart_85452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_85452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_85452 prefixEnd_85452 := by exact prefixLift 85452
  have htrace : WordTrace (prefixWord ++ tailWord_85452) baseStart_85452 baseEnd_85452 := by
    simpa [prefixWord, tailWord_85452, baseEnd_85452] using wordTrace_append hprefix tailTrace_85452
  have hstable : (prefixWord ++ tailWord_85452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85452).length < 2 ^ (prefixWord ++ tailWord_85452).sum := by decide
  have hdescent : baseEnd_85452 < baseStart_85452 := by decide
  rcases family_descends (prefixWord ++ tailWord_85452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85465 : List Nat := [1, 2, 1, 2, 4, 4, 1, 7]
def baseStart_85465 : Nat := 118140960795 + 85465 * 2 ^ 59
def prefixEnd_85465 : Nat := 4983230072969 + 3 ^ 40 * 85465 * 2
def baseEnd_85465 : Nat := 3250712899008396406997

theorem tailTrace_85465 : CollatzResearch.WordTrace tailWord_85465 prefixEnd_85465 3250712899008396406997 := by
  unfold tailWord_85465
  simp only [CollatzResearch.WordTrace]
  refine ⟨3117164635382376105041849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2078109756921584070027899 3117164635382376105041849)
  ·
    refine ⟨2337873476536782078781387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3117164635382376105041849 2337873476536782078781387)
    ·
      refine ⟨3506810214805173118172081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2337873476536782078781387 3506810214805173118172081)
      ·
        refine ⟨2630107661103879838629061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3506810214805173118172081 2630107661103879838629061)
        ·
          refine ⟨493145186456977469742949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2630107661103879838629061 493145186456977469742949)
          ·
            refine ⟨92464722460683275576803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 493145186456977469742949 92464722460683275576803)
            ·
              refine ⟨138697083691024913365205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92464722460683275576803 138697083691024913365205)
              ·
                refine ⟨3250712899008396406997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 138697083691024913365205 3250712899008396406997)
                ·
                  rfl

theorem cell22_85465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 7].length) (baseStart_85465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_85465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_85465 prefixEnd_85465 := by exact prefixLift 85465
  have htrace : WordTrace (prefixWord ++ tailWord_85465) baseStart_85465 baseEnd_85465 := by
    simpa [prefixWord, tailWord_85465, baseEnd_85465] using wordTrace_append hprefix tailTrace_85465
  have hstable : (prefixWord ++ tailWord_85465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85465).length < 2 ^ (prefixWord ++ tailWord_85465).sum := by decide
  have hdescent : baseEnd_85465 < baseStart_85465 := by decide
  rcases family_descends (prefixWord ++ tailWord_85465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85482 : List Nat := [3, 1, 3, 1, 4, 1, 3, 6]
def baseStart_85482 : Nat := 118140960795 + 85482 * 2 ^ 59
def prefixEnd_85482 : Nat := 4983230072969 + 3 ^ 40 * 85482 * 2
def baseEnd_85482 : Nat := 3251359504277021109769

theorem tailTrace_85482 : CollatzResearch.WordTrace tailWord_85482 prefixEnd_85482 3251359504277021109769 := by
  unfold tailWord_85482
  simp only [CollatzResearch.WordTrace]
  refine ⟨779446169080197002102675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2078523117547192005607133 779446169080197002102675)
  ·
    refine ⟨1169169253620295503154013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 779446169080197002102675 1169169253620295503154013)
    ·
      refine ⟨438438470107610813682755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1169169253620295503154013 438438470107610813682755)
      ·
        refine ⟨657657705161416220524133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 438438470107610813682755 657657705161416220524133)
        ·
          refine ⟨123310819717765541348275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 657657705161416220524133 123310819717765541348275)
          ·
            refine ⟨184966229576648312022413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123310819717765541348275 184966229576648312022413)
            ·
              refine ⟨69362336091243117008405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184966229576648312022413 69362336091243117008405)
              ·
                refine ⟨3251359504277021109769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 69362336091243117008405 3251359504277021109769)
                ·
                  rfl

theorem cell22_85482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 6].length) (baseStart_85482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_85482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_85482 prefixEnd_85482 := by exact prefixLift 85482
  have htrace : WordTrace (prefixWord ++ tailWord_85482) baseStart_85482 baseEnd_85482 := by
    simpa [prefixWord, tailWord_85482, baseEnd_85482] using wordTrace_append hprefix tailTrace_85482
  have hstable : (prefixWord ++ tailWord_85482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85482).length < 2 ^ (prefixWord ++ tailWord_85482).sum := by decide
  have hdescent : baseEnd_85482 < baseStart_85482 := by decide
  rcases family_descends (prefixWord ++ tailWord_85482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85514 : List Nat := [3, 1, 2, 2, 2, 2, 2, 4, 1, 3]
def baseStart_85514 : Nat := 118140960795 + 85514 * 2 ^ 59
def prefixEnd_85514 : Nat := 4983230072969 + 3 ^ 40 * 85514 * 2
def baseEnd_85514 : Nat := 29273189792455773187823

theorem tailTrace_85514 : CollatzResearch.WordTrace tailWord_85514 prefixEnd_85514 29273189792455773187823 := by
  unfold tailWord_85514
  simp only [CollatzResearch.WordTrace]
  refine ⟨779737953051214368393899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2079301208136571649050397 779737953051214368393899)
  ·
    refine ⟨1169606929576821552590849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 779737953051214368393899 1169606929576821552590849)
    ·
      refine ⟨877205197182616164443137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1169606929576821552590849 877205197182616164443137)
      ·
        refine ⟨657903897886962123332353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 877205197182616164443137 657903897886962123332353)
        ·
          refine ⟨493427923415221592499265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 657903897886962123332353 493427923415221592499265)
          ·
            refine ⟨370070942561416194374449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 493427923415221592499265 370070942561416194374449)
            ·
              refine ⟨277553206921062145780837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 370070942561416194374449 277553206921062145780837)
              ·
                refine ⟨52041226297699152333907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 277553206921062145780837 52041226297699152333907)
                ·
                  refine ⟨78061839446548728500861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52041226297699152333907 78061839446548728500861)
                  ·
                    refine ⟨29273189792455773187823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78061839446548728500861 29273189792455773187823)
                    ·
                      rfl

theorem cell22_85514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 4, 1, 3].length) (baseStart_85514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_85514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_85514 prefixEnd_85514 := by exact prefixLift 85514
  have htrace : WordTrace (prefixWord ++ tailWord_85514) baseStart_85514 baseEnd_85514 := by
    simpa [prefixWord, tailWord_85514, baseEnd_85514] using wordTrace_append hprefix tailTrace_85514
  have hstable : (prefixWord ++ tailWord_85514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85514).length < 2 ^ (prefixWord ++ tailWord_85514).sum := by decide
  have hdescent : baseEnd_85514 < baseStart_85514 := by decide
  rcases family_descends (prefixWord ++ tailWord_85514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85525 : List Nat := [1, 3, 2, 1, 3, 2, 2, 1, 2, 5]
def baseStart_85525 : Nat := 118140960795 + 85525 * 2 ^ 59
def prefixEnd_85525 : Nat := 4983230072969 + 3 ^ 40 * 85525 * 2
def baseEnd_85525 : Nat := 29276955317255411162789

theorem tailTrace_85525 : CollatzResearch.WordTrace tailWord_85525 prefixEnd_85525 29276955317255411162789 := by
  unfold tailWord_85525
  simp only [CollatzResearch.WordTrace]
  refine ⟨3119353015165006352226029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2079568676776670901484019 3119353015165006352226029)
  ·
    refine ⟨1169757380686877382084761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3119353015165006352226029 1169757380686877382084761)
    ·
      refine ⟨877318035515158036563571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1169757380686877382084761 877318035515158036563571)
      ·
        refine ⟨1315977053272737054845357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 877318035515158036563571 1315977053272737054845357)
        ·
          refine ⟨493491394977276395567009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1315977053272737054845357 493491394977276395567009)
          ·
            refine ⟨370118546232957296675257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 493491394977276395567009 370118546232957296675257)
            ·
              refine ⟨277588909674717972506443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 370118546232957296675257 277588909674717972506443)
              ·
                refine ⟨416383364512076958759665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 277588909674717972506443 416383364512076958759665)
                ·
                  refine ⟨312287523384057719069749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 416383364512076958759665 312287523384057719069749)
                  ·
                    refine ⟨29276955317255411162789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 312287523384057719069749 29276955317255411162789)
                    ·
                      rfl

theorem cell22_85525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_85525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_85525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_85525 prefixEnd_85525 := by exact prefixLift 85525
  have htrace : WordTrace (prefixWord ++ tailWord_85525) baseStart_85525 baseEnd_85525 := by
    simpa [prefixWord, tailWord_85525, baseEnd_85525] using wordTrace_append hprefix tailTrace_85525
  have hstable : (prefixWord ++ tailWord_85525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85525).length < 2 ^ (prefixWord ++ tailWord_85525).sum := by decide
  have hdescent : baseEnd_85525 < baseStart_85525 := by decide
  rcases family_descends (prefixWord ++ tailWord_85525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85557 : List Nat := [1, 3, 3, 1, 1, 3, 2, 3, 1, 4]
def baseStart_85557 : Nat := 118140960795 + 85557 * 2 ^ 59
def prefixEnd_85557 : Nat := 4983230072969 + 3 ^ 40 * 85557 * 2
def baseEnd_85557 : Nat := 29287909571217994362691

theorem tailTrace_85557 : CollatzResearch.WordTrace tailWord_85557 prefixEnd_85557 29287909571217994362691 := by
  unfold tailWord_85557
  simp only [CollatzResearch.WordTrace]
  refine ⟨3120520151049075817390925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2080346767366050544927283 3120520151049075817390925)
  ·
    refine ⟨1170195056643403431521597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3120520151049075817390925 1170195056643403431521597)
    ·
      refine ⟨438823146241276286820599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1170195056643403431521597 438823146241276286820599)
      ·
        refine ⟨658234719361914430230899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 438823146241276286820599 658234719361914430230899)
        ·
          refine ⟨987352079042871645346349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 658234719361914430230899 987352079042871645346349)
          ·
            refine ⟨370257029641076867004881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 987352079042871645346349 370257029641076867004881)
            ·
              refine ⟨277692772230807650253661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 370257029641076867004881 277692772230807650253661)
              ·
                refine ⟨104134789586552868845123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 277692772230807650253661 104134789586552868845123)
                ·
                  refine ⟨156202184379829303267685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104134789586552868845123 156202184379829303267685)
                  ·
                    refine ⟨29287909571217994362691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 156202184379829303267685 29287909571217994362691)
                    ·
                      rfl

theorem cell22_85557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_85557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_85557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_85557 prefixEnd_85557 := by exact prefixLift 85557
  have htrace : WordTrace (prefixWord ++ tailWord_85557) baseStart_85557 baseEnd_85557 := by
    simpa [prefixWord, tailWord_85557, baseEnd_85557] using wordTrace_append hprefix tailTrace_85557
  have hstable : (prefixWord ++ tailWord_85557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85557).length < 2 ^ (prefixWord ++ tailWord_85557).sum := by decide
  have hdescent : baseEnd_85557 < baseStart_85557 := by decide
  rcases family_descends (prefixWord ++ tailWord_85557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85585 : List Nat := [1, 2, 2, 1, 3, 2, 1, 2, 4, 4]
def baseStart_85585 : Nat := 118140960795 + 85585 * 2 ^ 59
def prefixEnd_85585 : Nat := 4983230072969 + 3 ^ 40 * 85585 * 2
def baseEnd_85585 : Nat := 29297494543435254662605

theorem tailTrace_85585 : CollatzResearch.WordTrace tailWord_85585 prefixEnd_85585 29297494543435254662605 := by
  unfold tailWord_85585
  simp only [CollatzResearch.WordTrace]
  refine ⟨3121541394947636599410209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2081027596631757732940139 3121541394947636599410209)
  ·
    refine ⟨2341156046210727449557657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3121541394947636599410209 2341156046210727449557657)
    ·
      refine ⟨1755867034658045587168243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2341156046210727449557657 1755867034658045587168243)
      ·
        refine ⟨2633800551987068380752365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1755867034658045587168243 2633800551987068380752365)
        ·
          refine ⟨987675206995150642782137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2633800551987068380752365 987675206995150642782137)
          ·
            refine ⟨740756405246362982086603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 987675206995150642782137 740756405246362982086603)
            ·
              refine ⟨1111134607869544473129905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 740756405246362982086603 1111134607869544473129905)
              ·
                refine ⟨833350955902158354847429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1111134607869544473129905 833350955902158354847429)
                ·
                  refine ⟨156253304231654691533893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 833350955902158354847429 156253304231654691533893)
                  ·
                    refine ⟨29297494543435254662605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 156253304231654691533893 29297494543435254662605)
                    ·
                      rfl

theorem cell22_85585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 4].length) (baseStart_85585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_85585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_85585 prefixEnd_85585 := by exact prefixLift 85585
  have htrace : WordTrace (prefixWord ++ tailWord_85585) baseStart_85585 baseEnd_85585 := by
    simpa [prefixWord, tailWord_85585, baseEnd_85585] using wordTrace_append hprefix tailTrace_85585
  have hstable : (prefixWord ++ tailWord_85585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85585).length < 2 ^ (prefixWord ++ tailWord_85585).sum := by decide
  have hdescent : baseEnd_85585 < baseStart_85585 := by decide
  rcases family_descends (prefixWord ++ tailWord_85585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85621 : List Nat := [1, 3, 4, 2, 1, 2, 2, 2, 2, 3]
def baseStart_85621 : Nat := 118140960795 + 85621 * 2 ^ 59
def prefixEnd_85621 : Nat := 4983230072969 + 3 ^ 40 * 85621 * 2
def baseEnd_85621 : Nat := 29309818079143160762495

theorem tailTrace_85621 : CollatzResearch.WordTrace tailWord_85621 prefixEnd_85621 29309818079143160762495 := by
  unfold tailWord_85621
  simp only [CollatzResearch.WordTrace]
  refine ⟨3122854422817214747720717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2081902948544809831813811 3122854422817214747720717)
  ·
    refine ⟨1171070408556455530395269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3122854422817214747720717 1171070408556455530395269)
    ·
      refine ⟨219575701604335411949113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1171070408556455530395269 219575701604335411949113)
      ·
        refine ⟨164681776203251558961835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219575701604335411949113 164681776203251558961835)
        ·
          refine ⟨247022664304877338442753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164681776203251558961835 247022664304877338442753)
          ·
            refine ⟨185266998228658003832065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 247022664304877338442753 185266998228658003832065)
            ·
              refine ⟨138950248671493502874049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185266998228658003832065 138950248671493502874049)
              ·
                refine ⟨104212686503620127155537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138950248671493502874049 104212686503620127155537)
                ·
                  refine ⟨78159514877715095366653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104212686503620127155537 78159514877715095366653)
                  ·
                    refine ⟨29309818079143160762495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78159514877715095366653 29309818079143160762495)
                    ·
                      rfl

theorem cell22_85621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_85621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_85621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_85621 prefixEnd_85621 := by exact prefixLift 85621
  have htrace : WordTrace (prefixWord ++ tailWord_85621) baseStart_85621 baseEnd_85621 := by
    simpa [prefixWord, tailWord_85621, baseEnd_85621] using wordTrace_append hprefix tailTrace_85621
  have hstable : (prefixWord ++ tailWord_85621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85621).length < 2 ^ (prefixWord ++ tailWord_85621).sum := by decide
  have hdescent : baseEnd_85621 < baseStart_85621 := by decide
  rcases family_descends (prefixWord ++ tailWord_85621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85632 : List Nat := [2, 1, 1, 2, 1, 4, 2, 3, 3, 3]
def baseStart_85632 : Nat := 118140960795 + 85632 * 2 ^ 59
def prefixEnd_85632 : Nat := 4983230072969 + 3 ^ 40 * 85632 * 2
def baseEnd_85632 : Nat := 29313583603942798737461

theorem tailTrace_85632 : CollatzResearch.WordTrace tailWord_85632 prefixEnd_85632 29313583603942798737461 := by
  unfold tailWord_85632
  simp only [CollatzResearch.WordTrace]
  refine ⟨1561627812888681813185575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2082170417184909084247433 1561627812888681813185575)
  ·
    refine ⟨2342441719333022719778363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1561627812888681813185575 2342441719333022719778363)
    ·
      refine ⟨3513662578999534079667545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2342441719333022719778363 3513662578999534079667545)
      ·
        refine ⟨2635246934249650559750659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3513662578999534079667545 2635246934249650559750659)
        ·
          refine ⟨3952870401374475839625989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2635246934249650559750659 3952870401374475839625989)
          ·
            refine ⟨741163200257714219929873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3952870401374475839625989 741163200257714219929873)
            ·
              refine ⟨555872400193285664947405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 741163200257714219929873 555872400193285664947405)
              ·
                refine ⟨208452150072482124355277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 555872400193285664947405 208452150072482124355277)
                ·
                  refine ⟨78169556277180796633229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 208452150072482124355277 78169556277180796633229)
                  ·
                    refine ⟨29313583603942798737461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78169556277180796633229 29313583603942798737461)
                    ·
                      rfl

theorem cell22_85632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 3, 3].length) (baseStart_85632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_85632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_85632 prefixEnd_85632 := by exact prefixLift 85632
  have htrace : WordTrace (prefixWord ++ tailWord_85632) baseStart_85632 baseEnd_85632 := by
    simpa [prefixWord, tailWord_85632, baseEnd_85632] using wordTrace_append hprefix tailTrace_85632
  have hstable : (prefixWord ++ tailWord_85632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85632).length < 2 ^ (prefixWord ++ tailWord_85632).sum := by decide
  have hdescent : baseEnd_85632 < baseStart_85632 := by decide
  rcases family_descends (prefixWord ++ tailWord_85632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85672 : List Nat := [2, 1, 7, 1, 2, 1, 1, 2, 2, 3]
def baseStart_85672 : Nat := 118140960795 + 85672 * 2 ^ 59
def prefixEnd_85672 : Nat := 4983230072969 + 3 ^ 40 * 85672 * 2
def baseEnd_85672 : Nat := 29327276421396027737339

theorem tailTrace_85672 : CollatzResearch.WordTrace tailWord_85672 prefixEnd_85672 29327276421396027737339 := by
  unfold tailWord_85672
  simp only [CollatzResearch.WordTrace]
  refine ⟨1562357272816225228913635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2083143030421633638551513 1562357272816225228913635)
  ·
    refine ⟨2343535909224337843370453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1562357272816225228913635 2343535909224337843370453)
    ·
      refine ⟨54926622872445418203995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 2343535909224337843370453 54926622872445418203995)
      ·
        refine ⟨82389934308668127305993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54926622872445418203995 82389934308668127305993)
        ·
          refine ⟨61792450731501095479495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82389934308668127305993 61792450731501095479495)
          ·
            refine ⟨92688676097251643219243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61792450731501095479495 92688676097251643219243)
            ·
              refine ⟨139033014145877464828865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92688676097251643219243 139033014145877464828865)
              ·
                refine ⟨104274760609408098621649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139033014145877464828865 104274760609408098621649)
                ·
                  refine ⟨78206070457056073966237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104274760609408098621649 78206070457056073966237)
                  ·
                    refine ⟨29327276421396027737339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78206070457056073966237 29327276421396027737339)
                    ·
                      rfl

theorem cell22_85672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_85672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_85672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_85672 prefixEnd_85672 := by exact prefixLift 85672
  have htrace : WordTrace (prefixWord ++ tailWord_85672) baseStart_85672 baseEnd_85672 := by
    simpa [prefixWord, tailWord_85672, baseEnd_85672] using wordTrace_append hprefix tailTrace_85672
  have hstable : (prefixWord ++ tailWord_85672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85672).length < 2 ^ (prefixWord ++ tailWord_85672).sum := by decide
  have hdescent : baseEnd_85672 < baseStart_85672 := by decide
  rcases family_descends (prefixWord ++ tailWord_85672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85677 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 4, 5]
def baseStart_85677 : Nat := 118140960795 + 85677 * 2 ^ 59
def prefixEnd_85677 : Nat := 4983230072969 + 3 ^ 40 * 85677 * 2
def baseEnd_85677 : Nat := 29328988023577681362323

theorem tailTrace_85677 : CollatzResearch.WordTrace tailWord_85677 prefixEnd_85677 29328988023577681362323 := by
  unfold tailWord_85677
  simp only [CollatzResearch.WordTrace]
  refine ⟨3124896910614336311759285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2083264607076224207839523 3124896910614336311759285)
  ·
    refine ⟨292959085370094029227433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3124896910614336311759285 292959085370094029227433)
    ·
      refine ⟨219719314027570521920575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292959085370094029227433 219719314027570521920575)
      ·
        refine ⟨329578971041355782880863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219719314027570521920575 329578971041355782880863)
        ·
          refine ⟨494368456562033674321295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329578971041355782880863 494368456562033674321295)
          ·
            refine ⟨741552684843050511481943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 494368456562033674321295 741552684843050511481943)
            ·
              refine ⟨1112329027264575767222915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 741552684843050511481943 1112329027264575767222915)
              ·
                refine ⟨1668493540896863650834373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1112329027264575767222915 1668493540896863650834373)
                ·
                  refine ⟨312842538918161934531445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1668493540896863650834373 312842538918161934531445)
                  ·
                    refine ⟨29328988023577681362323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 312842538918161934531445 29328988023577681362323)
                    ·
                      rfl

theorem cell22_85677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_85677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_85677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_85677 prefixEnd_85677 := by exact prefixLift 85677
  have htrace : WordTrace (prefixWord ++ tailWord_85677) baseStart_85677 baseEnd_85677 := by
    simpa [prefixWord, tailWord_85677, baseEnd_85677] using wordTrace_append hprefix tailTrace_85677
  have hstable : (prefixWord ++ tailWord_85677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85677).length < 2 ^ (prefixWord ++ tailWord_85677).sum := by decide
  have hdescent : baseEnd_85677 < baseStart_85677 := by decide
  rcases family_descends (prefixWord ++ tailWord_85677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85906 : List Nat := [3, 2, 3, 2, 1, 1, 1, 1, 4, 4]
def baseStart_85906 : Nat := 118140960795 + 85906 * 2 ^ 59
def prefixEnd_85906 : Nat := 4983230072969 + 3 ^ 40 * 85906 * 2
def baseEnd_85906 : Nat := 29407379403497417386621

theorem tailTrace_85906 : CollatzResearch.WordTrace tailWord_85906 prefixEnd_85906 29407379403497417386621 := by
  unfold tailWord_85906
  simp only [CollatzResearch.WordTrace]
  refine ⟨783312306696177105461393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2088832817856472281230381 783312306696177105461393)
  ·
    refine ⟨587484230022132829096045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 783312306696177105461393 587484230022132829096045)
    ·
      refine ⟨220306586258299810911017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 587484230022132829096045 220306586258299810911017)
      ·
        refine ⟨165229939693724858183263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 220306586258299810911017 165229939693724858183263)
        ·
          refine ⟨247844909540587287274895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165229939693724858183263 247844909540587287274895)
          ·
            refine ⟨371767364310880930912343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247844909540587287274895 371767364310880930912343)
            ·
              refine ⟨557651046466321396368515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 371767364310880930912343 557651046466321396368515)
              ·
                refine ⟨836476569699482094552773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 557651046466321396368515 836476569699482094552773)
                ·
                  refine ⟨156839356818652892728645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 836476569699482094552773 156839356818652892728645)
                  ·
                    refine ⟨29407379403497417386621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 156839356818652892728645 29407379403497417386621)
                    ·
                      rfl

theorem cell22_85906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_85906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_85906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_85906 prefixEnd_85906 := by exact prefixLift 85906
  have htrace : WordTrace (prefixWord ++ tailWord_85906) baseStart_85906 baseEnd_85906 := by
    simpa [prefixWord, tailWord_85906, baseEnd_85906] using wordTrace_append hprefix tailTrace_85906
  have hstable : (prefixWord ++ tailWord_85906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85906).length < 2 ^ (prefixWord ++ tailWord_85906).sum := by decide
  have hdescent : baseEnd_85906 < baseStart_85906 := by decide
  rcases family_descends (prefixWord ++ tailWord_85906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85921 : List Nat := [1, 2, 3, 4, 2, 1, 2, 7]
def baseStart_85921 : Nat := 118140960795 + 85921 * 2 ^ 59
def prefixEnd_85921 : Nat := 4983230072969 + 3 ^ 40 * 85921 * 2
def baseEnd_85921 : Nat := 3268057134449153140175

theorem tailTrace_85921 : CollatzResearch.WordTrace tailWord_85921 prefixEnd_85921 3268057134449153140175 := by
  unfold tailWord_85921
  simp only [CollatzResearch.WordTrace]
  refine ⟨3133796321730365983641617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2089197547820243989094411 3133796321730365983641617)
  ·
    refine ⟨2350347241297774487731213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3133796321730365983641617 2350347241297774487731213)
    ·
      refine ⟨881380215486665432899205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2350347241297774487731213 881380215486665432899205)
      ·
        refine ⟨165258790403749768668601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 881380215486665432899205 165258790403749768668601)
        ·
          refine ⟨123944092802812326501451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165258790403749768668601 123944092802812326501451)
          ·
            refine ⟨185916139204218489752177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123944092802812326501451 185916139204218489752177)
            ·
              refine ⟨139437104403163867314133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185916139204218489752177 139437104403163867314133)
              ·
                refine ⟨3268057134449153140175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 139437104403163867314133 3268057134449153140175)
                ·
                  rfl

theorem cell22_85921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 7].length) (baseStart_85921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_85921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_85921 prefixEnd_85921 := by exact prefixLift 85921
  have htrace : WordTrace (prefixWord ++ tailWord_85921) baseStart_85921 baseEnd_85921 := by
    simpa [prefixWord, tailWord_85921, baseEnd_85921] using wordTrace_append hprefix tailTrace_85921
  have hstable : (prefixWord ++ tailWord_85921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85921).length < 2 ^ (prefixWord ++ tailWord_85921).sum := by decide
  have hdescent : baseEnd_85921 < baseStart_85921 := by decide
  rcases family_descends (prefixWord ++ tailWord_85921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85940 : List Nat := [2, 5, 2, 1, 2, 1, 2, 1, 2, 4]
def baseStart_85940 : Nat := 118140960795 + 85940 * 2 ^ 59
def prefixEnd_85940 : Nat := 4983230072969 + 3 ^ 40 * 85940 * 2
def baseEnd_85940 : Nat := 29419018298332662036517

theorem tailTrace_85940 : CollatzResearch.WordTrace tailWord_85940 prefixEnd_85940 29419018298332662036517 := by
  unfold tailWord_85940
  simp only [CollatzResearch.WordTrace]
  refine ⟨1567244654330766114291637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2089659539107688152388849 1567244654330766114291637)
  ·
    refine ⟨146929186343509323214841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1567244654330766114291637 146929186343509323214841)
    ·
      refine ⟨110196889757631992411131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146929186343509323214841 110196889757631992411131)
      ·
        refine ⟨165295334636447988616697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110196889757631992411131 165295334636447988616697)
        ·
          refine ⟨123971500977335991462523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165295334636447988616697 123971500977335991462523)
          ·
            refine ⟨185957251466003987193785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123971500977335991462523 185957251466003987193785)
            ·
              refine ⟨139467938599502990395339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185957251466003987193785 139467938599502990395339)
              ·
                refine ⟨209201907899254485593009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139467938599502990395339 209201907899254485593009)
                ·
                  refine ⟨156901430924440864194757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 209201907899254485593009 156901430924440864194757)
                  ·
                    refine ⟨29419018298332662036517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 156901430924440864194757 29419018298332662036517)
                    ·
                      rfl

theorem cell22_85940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_85940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_85940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_85940 prefixEnd_85940 := by exact prefixLift 85940
  have htrace : WordTrace (prefixWord ++ tailWord_85940) baseStart_85940 baseEnd_85940 := by
    simpa [prefixWord, tailWord_85940, baseEnd_85940] using wordTrace_append hprefix tailTrace_85940
  have hstable : (prefixWord ++ tailWord_85940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85940).length < 2 ^ (prefixWord ++ tailWord_85940).sum := by decide
  have hdescent : baseEnd_85940 < baseStart_85940 := by decide
  rcases family_descends (prefixWord ++ tailWord_85940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85966 : List Nat := [4, 1, 1, 1, 2, 2, 4, 2, 5]
def baseStart_85966 : Nat := 118140960795 + 85966 * 2 ^ 59
def prefixEnd_85966 : Nat := 4983230072969 + 3 ^ 40 * 85966 * 2
def baseEnd_85966 : Nat := 9809306209892420295479

theorem tailTrace_85966 : CollatzResearch.WordTrace tailWord_85966 prefixEnd_85966 9809306209892420295479 := by
  unfold tailWord_85966
  simp only [CollatzResearch.WordTrace]
  refine ⟨391929700820917333628719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2090291737711559112686501 391929700820917333628719)
  ·
    refine ⟨587894551231376000443079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 391929700820917333628719 587894551231376000443079)
    ·
      refine ⟨881841826847064000664619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 587894551231376000443079 881841826847064000664619)
      ·
        refine ⟨1322762740270596000996929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 881841826847064000664619 1322762740270596000996929)
        ·
          refine ⟨992072055202947000747697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1322762740270596000996929 992072055202947000747697)
          ·
            refine ⟨744054041402210250560773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 992072055202947000747697 744054041402210250560773)
            ·
              refine ⟨139510132762914421980145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 744054041402210250560773 139510132762914421980145)
              ·
                refine ⟨104632599572185816485109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 139510132762914421980145 104632599572185816485109)
                ·
                  refine ⟨9809306209892420295479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 104632599572185816485109 9809306209892420295479)
                  ·
                    rfl

theorem cell22_85966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_85966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_85966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_85966 prefixEnd_85966 := by exact prefixLift 85966
  have htrace : WordTrace (prefixWord ++ tailWord_85966) baseStart_85966 baseEnd_85966 := by
    simpa [prefixWord, tailWord_85966, baseEnd_85966] using wordTrace_append hprefix tailTrace_85966
  have hstable : (prefixWord ++ tailWord_85966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85966).length < 2 ^ (prefixWord ++ tailWord_85966).sum := by decide
  have hdescent : baseEnd_85966 < baseStart_85966 := by decide
  rcases family_descends (prefixWord ++ tailWord_85966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86011 : List Nat := [1, 1, 1, 1, 1, 3, 5, 5, 4]
def baseStart_86011 : Nat := 118140960795 + 86011 * 2 ^ 59
def prefixEnd_86011 : Nat := 4983230072969 + 3 ^ 40 * 86011 * 2
def baseEnd_86011 : Nat := 9814441016437381170433

theorem tailTrace_86011 : CollatzResearch.WordTrace tailWord_86011 prefixEnd_86011 9814441016437381170433 := by
  unfold tailWord_86011
  simp only [CollatzResearch.WordTrace]
  refine ⟨3137078891404311354417887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2091385927602874236278591 3137078891404311354417887)
  ·
    refine ⟨4705618337106467031626831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3137078891404311354417887 4705618337106467031626831)
    ·
      refine ⟨7058427505659700547440247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4705618337106467031626831 7058427505659700547440247)
      ·
        refine ⟨10587641258489550821160371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7058427505659700547440247 10587641258489550821160371)
        ·
          refine ⟨15881461887734326231740557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10587641258489550821160371 15881461887734326231740557)
          ·
            refine ⟨5955548207900372336902709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15881461887734326231740557 5955548207900372336902709)
            ·
              refine ⟨558332644490659906584629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5955548207900372336902709 558332644490659906584629)
              ·
                refine ⟨52343685420999366242309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 558332644490659906584629 52343685420999366242309)
                ·
                  refine ⟨9814441016437381170433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52343685420999366242309 9814441016437381170433)
                  ·
                    rfl

theorem cell22_86011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5, 4].length) (baseStart_86011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_86011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_86011 prefixEnd_86011 := by exact prefixLift 86011
  have htrace : WordTrace (prefixWord ++ tailWord_86011) baseStart_86011 baseEnd_86011 := by
    simpa [prefixWord, tailWord_86011, baseEnd_86011] using wordTrace_append hprefix tailTrace_86011
  have hstable : (prefixWord ++ tailWord_86011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86011).length < 2 ^ (prefixWord ++ tailWord_86011).sum := by decide
  have hdescent : baseEnd_86011 < baseStart_86011 := by decide
  rcases family_descends (prefixWord ++ tailWord_86011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86013 : List Nat := [1, 4, 1, 1, 1, 2, 6, 1, 1, 4]
def baseStart_86013 : Nat := 118140960795 + 86013 * 2 ^ 59
def prefixEnd_86013 : Nat := 4983230072969 + 3 ^ 40 * 86013 * 2
def baseEnd_86013 : Nat := 29444007690184804961293

theorem tailTrace_86013 : CollatzResearch.WordTrace tailWord_86013 prefixEnd_86013 29444007690184804961293 := by
  unfold tailWord_86013
  simp only [CollatzResearch.WordTrace]
  refine ⟨3137151837397065695990693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2091434558264710463993795 3137151837397065695990693)
  ·
    refine ⟨588215969511949817998255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3137151837397065695990693 588215969511949817998255)
    ·
      refine ⟨882323954267924726997383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 588215969511949817998255 882323954267924726997383)
      ·
        refine ⟨1323485931401887090496075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 882323954267924726997383 1323485931401887090496075)
        ·
          refine ⟨1985228897102830635744113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1323485931401887090496075 1985228897102830635744113)
          ·
            refine ⟨1488921672827122976808085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1985228897102830635744113 1488921672827122976808085)
            ·
              refine ⟨69793203413771389537879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1488921672827122976808085 69793203413771389537879)
              ·
                refine ⟨104689805120657084306819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69793203413771389537879 104689805120657084306819)
                ·
                  refine ⟨157034707680985626460229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104689805120657084306819 157034707680985626460229)
                  ·
                    refine ⟨29444007690184804961293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 157034707680985626460229 29444007690184804961293)
                    ·
                      rfl

theorem cell22_86013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 1, 4].length) (baseStart_86013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_86013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_86013 prefixEnd_86013 := by exact prefixLift 86013
  have htrace : WordTrace (prefixWord ++ tailWord_86013) baseStart_86013 baseEnd_86013 := by
    simpa [prefixWord, tailWord_86013, baseEnd_86013] using wordTrace_append hprefix tailTrace_86013
  have hstable : (prefixWord ++ tailWord_86013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86013).length < 2 ^ (prefixWord ++ tailWord_86013).sum := by decide
  have hdescent : baseEnd_86013 < baseStart_86013 := by decide
  rcases family_descends (prefixWord ++ tailWord_86013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86071 : List Nat := [1, 1, 3, 1, 2, 2, 2, 2, 5, 3]
def baseStart_86071 : Nat := 118140960795 + 86071 * 2 ^ 59
def prefixEnd_86071 : Nat := 4983230072969 + 3 ^ 40 * 86071 * 2
def baseEnd_86071 : Nat := 29463862275491987011115

theorem tailTrace_86071 : CollatzResearch.WordTrace tailWord_86071 prefixEnd_86071 29463862275491987011115 := by
  unfold tailWord_86071
  simp only [CollatzResearch.WordTrace]
  refine ⟨3139267271186941601602067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2092844847457961067734711 3139267271186941601602067)
  ·
    refine ⟨4708900906780412402403101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3139267271186941601602067 4708900906780412402403101)
    ·
      refine ⟨1765837840042654650901163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4708900906780412402403101 1765837840042654650901163)
      ·
        refine ⟨2648756760063981976351745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1765837840042654650901163 2648756760063981976351745)
        ·
          refine ⟨1986567570047986482263809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2648756760063981976351745 1986567570047986482263809)
          ·
            refine ⟨1489925677535989861697857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1986567570047986482263809 1489925677535989861697857)
            ·
              refine ⟨1117444258151992396273393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1489925677535989861697857 1117444258151992396273393)
              ·
                refine ⟨838083193613994297205045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1117444258151992396273393 838083193613994297205045)
                ·
                  refine ⟨78570299401311965362973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 838083193613994297205045 78570299401311965362973)
                  ·
                    refine ⟨29463862275491987011115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78570299401311965362973 29463862275491987011115)
                    ·
                      rfl

theorem cell22_86071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 5, 3].length) (baseStart_86071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_86071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_86071 prefixEnd_86071 := by exact prefixLift 86071
  have htrace : WordTrace (prefixWord ++ tailWord_86071) baseStart_86071 baseEnd_86071 := by
    simpa [prefixWord, tailWord_86071, baseEnd_86071] using wordTrace_append hprefix tailTrace_86071
  have hstable : (prefixWord ++ tailWord_86071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86071).length < 2 ^ (prefixWord ++ tailWord_86071).sum := by decide
  have hdescent : baseEnd_86071 < baseStart_86071 := by decide
  rcases family_descends (prefixWord ++ tailWord_86071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86073 : List Nat := [1, 2, 1, 5, 4, 1, 8]
def baseStart_86073 : Nat := 118140960795 + 86073 * 2 ^ 59
def prefixEnd_86073 : Nat := 4983230072969 + 3 ^ 40 * 86073 * 2
def baseEnd_86073 : Nat := 1091279515420912905967

theorem tailTrace_86073 : CollatzResearch.WordTrace tailWord_86073 prefixEnd_86073 1091279515420912905967 := by
  unfold tailWord_86073
  simp only [CollatzResearch.WordTrace]
  refine ⟨3139340217179695943174873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2092893478119797295449915 3139340217179695943174873)
  ·
    refine ⟨2354505162884771957381155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3139340217179695943174873 2354505162884771957381155)
    ·
      refine ⟨3531757744327157936071733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2354505162884771957381155 3531757744327157936071733)
      ·
        refine ⟨331102288530671056506725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3531757744327157936071733 331102288530671056506725)
        ·
          refine ⟨62081679099500823095011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 331102288530671056506725 62081679099500823095011)
          ·
            refine ⟨93122518649251234642517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62081679099500823095011 93122518649251234642517)
            ·
              refine ⟨1091279515420912905967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 93122518649251234642517 1091279515420912905967)
              ·
                rfl

theorem cell22_86073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 8].length) (baseStart_86073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_86073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_86073 prefixEnd_86073 := by exact prefixLift 86073
  have htrace : WordTrace (prefixWord ++ tailWord_86073) baseStart_86073 baseEnd_86073 := by
    simpa [prefixWord, tailWord_86073, baseEnd_86073] using wordTrace_append hprefix tailTrace_86073
  have hstable : (prefixWord ++ tailWord_86073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86073).length < 2 ^ (prefixWord ++ tailWord_86073).sum := by decide
  have hdescent : baseEnd_86073 < baseStart_86073 := by decide
  rcases family_descends (prefixWord ++ tailWord_86073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86223 : List Nat := [1, 1, 2, 1, 1, 3, 3, 4, 3, 3]
def baseStart_86223 : Nat := 118140960795 + 86223 * 2 ^ 59
def prefixEnd_86223 : Nat := 4983230072969 + 3 ^ 40 * 86223 * 2
def baseEnd_86223 : Nat := 29515894981814257210649

theorem tailTrace_86223 : CollatzResearch.WordTrace tailWord_86223 prefixEnd_86223 29515894981814257210649 := by
  unfold tailWord_86223
  simp only [CollatzResearch.WordTrace]
  refine ⟨3144811166636271561135323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2096540777757514374090215 3144811166636271561135323)
  ·
    refine ⟨4717216749954407341702985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3144811166636271561135323 4717216749954407341702985)
    ·
      refine ⟨3537912562465805506277239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4717216749954407341702985 3537912562465805506277239)
      ·
        refine ⟨5306868843698708259415859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3537912562465805506277239 5306868843698708259415859)
        ·
          refine ⟨7960303265548062389123789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5306868843698708259415859 7960303265548062389123789)
          ·
            refine ⟨2985113724580523395921421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7960303265548062389123789 2985113724580523395921421)
            ·
              refine ⟨1119417646717696273470533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2985113724580523395921421 1119417646717696273470533)
              ·
                refine ⟨209890808759568051275725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1119417646717696273470533 209890808759568051275725)
                ·
                  refine ⟨78709053284838019228397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 209890808759568051275725 78709053284838019228397)
                  ·
                    refine ⟨29515894981814257210649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78709053284838019228397 29515894981814257210649)
                    ·
                      rfl

theorem cell22_86223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 3, 3].length) (baseStart_86223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_86223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_86223 prefixEnd_86223 := by exact prefixLift 86223
  have htrace : WordTrace (prefixWord ++ tailWord_86223) baseStart_86223 baseEnd_86223 := by
    simpa [prefixWord, tailWord_86223, baseEnd_86223] using wordTrace_append hprefix tailTrace_86223
  have hstable : (prefixWord ++ tailWord_86223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86223).length < 2 ^ (prefixWord ++ tailWord_86223).sum := by decide
  have hdescent : baseEnd_86223 < baseStart_86223 := by decide
  rcases family_descends (prefixWord ++ tailWord_86223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86270 : List Nat := [4, 2, 2, 1, 1, 1, 3, 3, 5]
def baseStart_86270 : Nat := 118140960795 + 86270 * 2 ^ 59
def prefixEnd_86270 : Nat := 4983230072969 + 3 ^ 40 * 86270 * 2
def baseEnd_86270 : Nat := 9843994680773933761835

theorem tailTrace_86270 : CollatzResearch.WordTrace tailWord_86270 prefixEnd_86270 9843994680773933761835 := by
  unfold tailWord_86270
  simp only [CollatzResearch.WordTrace]
  refine ⟨393315674683249823512033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2097683598310665725397509 393315674683249823512033)
  ·
    refine ⟨294986756012437367634025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 393315674683249823512033 294986756012437367634025)
    ·
      refine ⟨221240067009328025725519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294986756012437367634025 221240067009328025725519)
      ·
        refine ⟨331860100513992038588279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221240067009328025725519 331860100513992038588279)
        ·
          refine ⟨497790150770988057882419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331860100513992038588279 497790150770988057882419)
          ·
            refine ⟨746685226156482086823629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 497790150770988057882419 746685226156482086823629)
            ·
              refine ⟨280006959808680782558861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 746685226156482086823629 280006959808680782558861)
              ·
                refine ⟨105002609928255293459573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 280006959808680782558861 105002609928255293459573)
                ·
                  refine ⟨9843994680773933761835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 105002609928255293459573 9843994680773933761835)
                  ·
                    rfl

theorem cell22_86270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_86270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_86270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_86270 prefixEnd_86270 := by exact prefixLift 86270
  have htrace : WordTrace (prefixWord ++ tailWord_86270) baseStart_86270 baseEnd_86270 := by
    simpa [prefixWord, tailWord_86270, baseEnd_86270] using wordTrace_append hprefix tailTrace_86270
  have hstable : (prefixWord ++ tailWord_86270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86270).length < 2 ^ (prefixWord ++ tailWord_86270).sum := by decide
  have hdescent : baseEnd_86270 < baseStart_86270 := by decide
  rcases family_descends (prefixWord ++ tailWord_86270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86283 : List Nat := [1, 1, 1, 1, 5, 2, 3, 1, 3, 4]
def baseStart_86283 : Nat := 118140960795 + 86283 * 2 ^ 59
def prefixEnd_86283 : Nat := 4983230072969 + 3 ^ 40 * 86283 * 2
def baseEnd_86283 : Nat := 29536434207994100710465

theorem tailTrace_86283 : CollatzResearch.WordTrace tailWord_86283 prefixEnd_86283 29536434207994100710465 := by
  unfold tailWord_86283
  simp only [CollatzResearch.WordTrace]
  refine ⟨3146999546418901808319503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2097999697612601205546335 3146999546418901808319503)
  ·
    refine ⟨4720499319628352712479255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3146999546418901808319503 4720499319628352712479255)
    ·
      refine ⟨7080748979442529068718883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4720499319628352712479255 7080748979442529068718883)
      ·
        refine ⟨10621123469163793603078325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7080748979442529068718883 10621123469163793603078325)
        ·
          refine ⟨995730325234105650288593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10621123469163793603078325 995730325234105650288593)
          ·
            refine ⟨746797743925579237716445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 995730325234105650288593 746797743925579237716445)
            ·
              refine ⟨280049153972092214143667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 746797743925579237716445 280049153972092214143667)
              ·
                refine ⟨420073730958138321215501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280049153972092214143667 420073730958138321215501)
                ·
                  refine ⟨157527649109301870455813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 420073730958138321215501 157527649109301870455813)
                  ·
                    refine ⟨29536434207994100710465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 157527649109301870455813 29536434207994100710465)
                    ·
                      rfl

theorem cell22_86283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 4].length) (baseStart_86283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_86283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_86283 prefixEnd_86283 := by exact prefixLift 86283
  have htrace : WordTrace (prefixWord ++ tailWord_86283) baseStart_86283 baseEnd_86283 := by
    simpa [prefixWord, tailWord_86283, baseEnd_86283] using wordTrace_append hprefix tailTrace_86283
  have hstable : (prefixWord ++ tailWord_86283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86283).length < 2 ^ (prefixWord ++ tailWord_86283).sum := by decide
  have hdescent : baseEnd_86283 < baseStart_86283 := by decide
  rcases family_descends (prefixWord ++ tailWord_86283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86328 : List Nat := [2, 1, 2, 1, 3, 1, 2, 2, 4, 4]
def baseStart_86328 : Nat := 118140960795 + 86328 * 2 ^ 59
def prefixEnd_86328 : Nat := 4983230072969 + 3 ^ 40 * 86328 * 2
def baseEnd_86328 : Nat := 29551838627628983335327

theorem tailTrace_86328 : CollatzResearch.WordTrace tailWord_86328 prefixEnd_86328 29551838627628983335327 := by
  unfold tailWord_86328
  simp only [CollatzResearch.WordTrace]
  refine ⟨1574320415627937246853819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2099093887503916329138425 1574320415627937246853819)
  ·
    refine ⟨2361480623441905870280729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1574320415627937246853819 2361480623441905870280729)
    ·
      refine ⟨1771110467581429402710547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2361480623441905870280729 1771110467581429402710547)
      ·
        refine ⟨2656665701372144104065821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1771110467581429402710547 2656665701372144104065821)
        ·
          refine ⟨996249638014554039024683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2656665701372144104065821 996249638014554039024683)
          ·
            refine ⟨1494374457021831058537025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 996249638014554039024683 1494374457021831058537025)
            ·
              refine ⟨1120780842766373293902769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1494374457021831058537025 1120780842766373293902769)
              ·
                refine ⟨840585632074779970427077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1120780842766373293902769 840585632074779970427077)
                ·
                  refine ⟨157609806014021244455077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 840585632074779970427077 157609806014021244455077)
                  ·
                    refine ⟨29551838627628983335327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 157609806014021244455077 29551838627628983335327)
                    ·
                      rfl

theorem cell22_86328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 4, 4].length) (baseStart_86328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_86328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_86328 prefixEnd_86328 := by exact prefixLift 86328
  have htrace : WordTrace (prefixWord ++ tailWord_86328) baseStart_86328 baseEnd_86328 := by
    simpa [prefixWord, tailWord_86328, baseEnd_86328] using wordTrace_append hprefix tailTrace_86328
  have hstable : (prefixWord ++ tailWord_86328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86328).length < 2 ^ (prefixWord ++ tailWord_86328).sum := by decide
  have hdescent : baseEnd_86328 < baseStart_86328 := by decide
  rcases family_descends (prefixWord ++ tailWord_86328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86330 : List Nat := [3, 1, 1, 1, 4, 3, 2, 1, 1, 5]
def baseStart_86330 : Nat := 118140960795 + 86330 * 2 ^ 59
def prefixEnd_86330 : Nat := 4983230072969 + 3 ^ 40 * 86330 * 2
def baseEnd_86330 : Nat := 29552523268501644785321

theorem tailTrace_86330 : CollatzResearch.WordTrace tailWord_86330 prefixEnd_86330 29552523268501644785321 := by
  unfold tailWord_86330
  simp only [CollatzResearch.WordTrace]
  refine ⟨787178444312157208820111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2099142518165752556853629 787178444312157208820111)
  ·
    refine ⟨1180767666468235813230167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 787178444312157208820111 1180767666468235813230167)
    ·
      refine ⟨1771151499702353719845251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1180767666468235813230167 1771151499702353719845251)
      ·
        refine ⟨2656727249553530579767877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1771151499702353719845251 2656727249553530579767877)
        ·
          refine ⟨498136359291286983706477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2656727249553530579767877 498136359291286983706477)
          ·
            refine ⟨186801134734232618889929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 498136359291286983706477 186801134734232618889929)
            ·
              refine ⟨140100851050674464167447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186801134734232618889929 140100851050674464167447)
              ·
                refine ⟨210151276576011696251171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140100851050674464167447 210151276576011696251171)
                ·
                  refine ⟨315226914864017544376757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 210151276576011696251171 315226914864017544376757)
                  ·
                    refine ⟨29552523268501644785321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 315226914864017544376757 29552523268501644785321)
                    ·
                      rfl

theorem cell22_86330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 1, 5].length) (baseStart_86330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_86330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_86330 prefixEnd_86330 := by exact prefixLift 86330
  have htrace : WordTrace (prefixWord ++ tailWord_86330) baseStart_86330 baseEnd_86330 := by
    simpa [prefixWord, tailWord_86330, baseEnd_86330] using wordTrace_append hprefix tailTrace_86330
  have hstable : (prefixWord ++ tailWord_86330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86330).length < 2 ^ (prefixWord ++ tailWord_86330).sum := by decide
  have hdescent : baseEnd_86330 < baseStart_86330 := by decide
  rcases family_descends (prefixWord ++ tailWord_86330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86364 : List Nat := [2, 2, 4, 3, 1, 1, 1, 1, 4, 3]
def baseStart_86364 : Nat := 118140960795 + 86364 * 2 ^ 59
def prefixEnd_86364 : Nat := 4983230072969 + 3 ^ 40 * 86364 * 2
def baseEnd_86364 : Nat := 29564162163336889435217

theorem tailTrace_86364 : CollatzResearch.WordTrace tailWord_86364 prefixEnd_86364 29564162163336889435217 := by
  unfold tailWord_86364
  simp only [CollatzResearch.WordTrace]
  refine ⟨1574976929562726321009073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2099969239416968428012097 1574976929562726321009073)
  ·
    refine ⟨1181232697172044740756805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1574976929562726321009073 1181232697172044740756805)
    ·
      refine ⟨221481130719758388891901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1181232697172044740756805 221481130719758388891901)
      ·
        refine ⟨83055424019909395834463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 221481130719758388891901 83055424019909395834463)
        ·
          refine ⟨124583136029864093751695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83055424019909395834463 124583136029864093751695)
          ·
            refine ⟨186874704044796140627543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124583136029864093751695 186874704044796140627543)
            ·
              refine ⟨280312056067194210941315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 186874704044796140627543 280312056067194210941315)
              ·
                refine ⟨420468084100791316411973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280312056067194210941315 420468084100791316411973)
                ·
                  refine ⟨78837765768898371827245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 420468084100791316411973 78837765768898371827245)
                  ·
                    refine ⟨29564162163336889435217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78837765768898371827245 29564162163336889435217)
                    ·
                      rfl

theorem cell22_86364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_86364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_86364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_86364 prefixEnd_86364 := by exact prefixLift 86364
  have htrace : WordTrace (prefixWord ++ tailWord_86364) baseStart_86364 baseEnd_86364 := by
    simpa [prefixWord, tailWord_86364, baseEnd_86364] using wordTrace_append hprefix tailTrace_86364
  have hstable : (prefixWord ++ tailWord_86364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86364).length < 2 ^ (prefixWord ++ tailWord_86364).sum := by decide
  have hdescent : baseEnd_86364 < baseStart_86364 := by decide
  rcases family_descends (prefixWord ++ tailWord_86364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86409 : List Nat := [1, 2, 1, 1, 6, 1, 3, 3, 1, 3]
def baseStart_86409 : Nat := 118140960795 + 86409 * 2 ^ 59
def prefixEnd_86409 : Nat := 4983230072969 + 3 ^ 40 * 86409 * 2
def baseEnd_86409 : Nat := 29579566582971772060079

theorem tailTrace_86409 : CollatzResearch.WordTrace tailWord_86409 prefixEnd_86409 29579566582971772060079 := by
  unfold tailWord_86409
  simp only [CollatzResearch.WordTrace]
  refine ⟨3151595143962425327406281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2101063429308283551604187 3151595143962425327406281)
  ·
    refine ⟨2363696357971818995554711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3151595143962425327406281 2363696357971818995554711)
    ·
      refine ⟨3545544536957728493332067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2363696357971818995554711 3545544536957728493332067)
      ·
        refine ⟨5318316805436592739998101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3545544536957728493332067 5318316805436592739998101)
        ·
          refine ⟨249296100254840284687411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5318316805436592739998101 249296100254840284687411)
          ·
            refine ⟨373944150382260427031117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249296100254840284687411 373944150382260427031117)
            ·
              refine ⟨140229056393347660136669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 373944150382260427031117 140229056393347660136669)
              ·
                refine ⟨52585896147505372551251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140229056393347660136669 52585896147505372551251)
                ·
                  refine ⟨78878844221258058826877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52585896147505372551251 78878844221258058826877)
                  ·
                    refine ⟨29579566582971772060079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78878844221258058826877 29579566582971772060079)
                    ·
                      rfl

theorem cell22_86409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 3, 1, 3].length) (baseStart_86409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_86409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_86409 prefixEnd_86409 := by exact prefixLift 86409
  have htrace : WordTrace (prefixWord ++ tailWord_86409) baseStart_86409 baseEnd_86409 := by
    simpa [prefixWord, tailWord_86409, baseEnd_86409] using wordTrace_append hprefix tailTrace_86409
  have hstable : (prefixWord ++ tailWord_86409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86409).length < 2 ^ (prefixWord ++ tailWord_86409).sum := by decide
  have hdescent : baseEnd_86409 < baseStart_86409 := by decide
  rcases family_descends (prefixWord ++ tailWord_86409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86426 : List Nat := [3, 1, 1, 4, 1, 3, 3, 2, 1, 3]
def baseStart_86426 : Nat := 118140960795 + 86426 * 2 ^ 59
def prefixEnd_86426 : Nat := 4983230072969 + 3 ^ 40 * 86426 * 2
def baseEnd_86426 : Nat := 29585386030389394385027

theorem tailTrace_86426 : CollatzResearch.WordTrace tailWord_86426 prefixEnd_86426 29585386030389394385027 := by
  unfold tailWord_86426
  simp only [CollatzResearch.WordTrace]
  refine ⟨788053796225209307693783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2101476789933891487183421 788053796225209307693783)
  ·
    refine ⟨1182080694337813961540675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 788053796225209307693783 1182080694337813961540675)
    ·
      refine ⟨1773121041506720942311013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1182080694337813961540675 1773121041506720942311013)
      ·
        refine ⟨332460195282510176683315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1773121041506720942311013 332460195282510176683315)
        ·
          refine ⟨498690292923765265024973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332460195282510176683315 498690292923765265024973)
          ·
            refine ⟨187008859846411974384365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 498690292923765265024973 187008859846411974384365)
            ·
              refine ⟨70128322442404490394137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 187008859846411974384365 70128322442404490394137)
              ·
                refine ⟨52596241831803367795603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70128322442404490394137 52596241831803367795603)
                ·
                  refine ⟨78894362747705051693405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52596241831803367795603 78894362747705051693405)
                  ·
                    refine ⟨29585386030389394385027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 78894362747705051693405 29585386030389394385027)
                    ·
                      rfl

theorem cell22_86426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 2, 1, 3].length) (baseStart_86426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_86426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_86426 prefixEnd_86426 := by exact prefixLift 86426
  have htrace : WordTrace (prefixWord ++ tailWord_86426) baseStart_86426 baseEnd_86426 := by
    simpa [prefixWord, tailWord_86426, baseEnd_86426] using wordTrace_append hprefix tailTrace_86426
  have hstable : (prefixWord ++ tailWord_86426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86426).length < 2 ^ (prefixWord ++ tailWord_86426).sum := by decide
  have hdescent : baseEnd_86426 < baseStart_86426 := by decide
  rcases family_descends (prefixWord ++ tailWord_86426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86439 : List Nat := [1, 1, 6, 1, 1, 4, 2, 1, 5]
def baseStart_86439 : Nat := 118140960795 + 86439 * 2 ^ 59
def prefixEnd_86439 : Nat := 4983230072969 + 3 ^ 40 * 86439 * 2
def baseEnd_86439 : Nat := 9863278732020564603329

theorem tailTrace_86439 : CollatzResearch.WordTrace tailWord_86439 prefixEnd_86439 9863278732020564603329 := by
  unfold tailWord_86439
  simp only [CollatzResearch.WordTrace]
  refine ⟨3152689333853740450998371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2101792889235826967332247 3152689333853740450998371)
  ·
    refine ⟨4729034000780610676497557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3152689333853740450998371 4729034000780610676497557)
    ·
      refine ⟨221673468786591125460823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4729034000780610676497557 221673468786591125460823)
      ·
        refine ⟨332510203179886688191235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221673468786591125460823 332510203179886688191235)
        ·
          refine ⟨498765304769830032286853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332510203179886688191235 498765304769830032286853)
          ·
            refine ⟨93518494644343131053785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 498765304769830032286853 93518494644343131053785)
            ·
              refine ⟨70138870983257348290339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93518494644343131053785 70138870983257348290339)
              ·
                refine ⟨105208306474886022435509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70138870983257348290339 105208306474886022435509)
                ·
                  refine ⟨9863278732020564603329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 105208306474886022435509 9863278732020564603329)
                  ·
                    rfl

theorem cell22_86439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 5].length) (baseStart_86439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_86439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_86439 prefixEnd_86439 := by exact prefixLift 86439
  have htrace : WordTrace (prefixWord ++ tailWord_86439) baseStart_86439 baseEnd_86439 := by
    simpa [prefixWord, tailWord_86439, baseEnd_86439] using wordTrace_append hprefix tailTrace_86439
  have hstable : (prefixWord ++ tailWord_86439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86439).length < 2 ^ (prefixWord ++ tailWord_86439).sum := by decide
  have hdescent : baseEnd_86439 < baseStart_86439 := by decide
  rcases family_descends (prefixWord ++ tailWord_86439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86484 : List Nat := [2, 4, 1, 2, 2, 2, 1, 4, 4]
def baseStart_86484 : Nat := 118140960795 + 86484 * 2 ^ 59
def prefixEnd_86484 : Nat := 4983230072969 + 3 ^ 40 * 86484 * 2
def baseEnd_86484 : Nat := 9868413538565525478283

theorem tailTrace_86484 : CollatzResearch.WordTrace tailWord_86484 prefixEnd_86484 9868413538565525478283 := by
  unfold tailWord_86484
  simp only [CollatzResearch.WordTrace]
  refine ⟨1577165309345356568193253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2102887079127142090924337 1577165309345356568193253)
  ·
    refine ⟨295718495502254356536235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1577165309345356568193253 295718495502254356536235)
    ·
      refine ⟨443577743253381534804353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295718495502254356536235 443577743253381534804353)
      ·
        refine ⟨332683307440036151103265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 443577743253381534804353 332683307440036151103265)
        ·
          refine ⟨249512480580027113327449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 332683307440036151103265 249512480580027113327449)
          ·
            refine ⟨187134360435020334995587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 249512480580027113327449 187134360435020334995587)
            ·
              refine ⟨280701540652530502493381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187134360435020334995587 280701540652530502493381)
              ·
                refine ⟨52631538872349469217509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 280701540652530502493381 52631538872349469217509)
                ·
                  refine ⟨9868413538565525478283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52631538872349469217509 9868413538565525478283)
                  ·
                    rfl

theorem cell22_86484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_86484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_86484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_86484 prefixEnd_86484 := by exact prefixLift 86484
  have htrace : WordTrace (prefixWord ++ tailWord_86484) baseStart_86484 baseEnd_86484 := by
    simpa [prefixWord, tailWord_86484, baseEnd_86484] using wordTrace_append hprefix tailTrace_86484
  have hstable : (prefixWord ++ tailWord_86484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86484).length < 2 ^ (prefixWord ++ tailWord_86484).sum := by decide
  have hdescent : baseEnd_86484 < baseStart_86484 := by decide
  rcases family_descends (prefixWord ++ tailWord_86484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86495 : List Nat := [1, 1, 2, 3, 3, 2, 3, 7]
def baseStart_86495 : Nat := 118140960795 + 86495 * 2 ^ 59
def prefixEnd_86495 : Nat := 4983230072969 + 3 ^ 40 * 86495 * 2
def baseEnd_86495 : Nat := 3289889571166246045535

theorem tailTrace_86495 : CollatzResearch.WordTrace tailWord_86495 prefixEnd_86495 3289889571166246045535 := by
  unfold tailWord_86495
  simp only [CollatzResearch.WordTrace]
  refine ⟨3154731821650862015036939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2103154547767241343357959 3154731821650862015036939)
  ·
    refine ⟨4732097732476293022555409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3154731821650862015036939 4732097732476293022555409)
    ·
      refine ⟨3549073299357219766916557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4732097732476293022555409 3549073299357219766916557)
      ·
        refine ⟨1330902487258957412593709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3549073299357219766916557 1330902487258957412593709)
        ·
          refine ⟨499088432722109029722641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1330902487258957412593709 499088432722109029722641)
          ·
            refine ⟨374316324541581772291981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 499088432722109029722641 374316324541581772291981)
            ·
              refine ⟨140368621703093164609493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 374316324541581772291981 140368621703093164609493)
              ·
                refine ⟨3289889571166246045535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 140368621703093164609493 3289889571166246045535)
                ·
                  rfl

theorem cell22_86495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 7].length) (baseStart_86495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_86495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_86495 prefixEnd_86495 := by exact prefixLift 86495
  have htrace : WordTrace (prefixWord ++ tailWord_86495) baseStart_86495 baseEnd_86495 := by
    simpa [prefixWord, tailWord_86495, baseEnd_86495] using wordTrace_append hprefix tailTrace_86495
  have hstable : (prefixWord ++ tailWord_86495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86495).length < 2 ^ (prefixWord ++ tailWord_86495).sum := by decide
  have hdescent : baseEnd_86495 < baseStart_86495 := by decide
  rcases family_descends (prefixWord ++ tailWord_86495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86602 : List Nat := [3, 1, 2, 1, 1, 4, 3, 1, 6]
def baseStart_86602 : Nat := 118140960795 + 86602 * 2 ^ 59
def prefixEnd_86602 : Nat := 4983230072969 + 3 ^ 40 * 86602 * 2
def baseEnd_86602 : Nat := 9881878142394533994829

theorem tailTrace_86602 : CollatzResearch.WordTrace tailWord_86602 prefixEnd_86602 9881878142394533994829 := by
  unfold tailWord_86602
  simp only [CollatzResearch.WordTrace]
  refine ⟨789658608065804822295515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2105756288175479526121373 789658608065804822295515)
  ·
    refine ⟨1184487912098707233443273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 789658608065804822295515 1184487912098707233443273)
    ·
      refine ⟨888365934074030425082455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1184487912098707233443273 888365934074030425082455)
      ·
        refine ⟨1332548901111045637623683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 888365934074030425082455 1332548901111045637623683)
        ·
          refine ⟨1998823351666568456435525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1332548901111045637623683 1998823351666568456435525)
          ·
            refine ⟨374779378437481585581661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1998823351666568456435525 374779378437481585581661)
            ·
              refine ⟨140542266914055594593123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 374779378437481585581661 140542266914055594593123)
              ·
                refine ⟨210813400371083391889685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140542266914055594593123 210813400371083391889685)
                ·
                  refine ⟨9881878142394533994829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 210813400371083391889685 9881878142394533994829)
                  ·
                    rfl

theorem cell22_86602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 6].length) (baseStart_86602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_86602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_86602 prefixEnd_86602 := by exact prefixLift 86602
  have htrace : WordTrace (prefixWord ++ tailWord_86602) baseStart_86602 baseEnd_86602 := by
    simpa [prefixWord, tailWord_86602, baseEnd_86602] using wordTrace_append hprefix tailTrace_86602
  have hstable : (prefixWord ++ tailWord_86602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86602).length < 2 ^ (prefixWord ++ tailWord_86602).sum := by decide
  have hdescent : baseEnd_86602 < baseStart_86602 := by decide
  rcases family_descends (prefixWord ++ tailWord_86602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86653 : List Nat := [1, 4, 1, 1, 5, 2, 2, 2, 4]
def baseStart_86653 : Nat := 118140960795 + 86653 * 2 ^ 59
def prefixEnd_86653 : Nat := 4983230072969 + 3 ^ 40 * 86653 * 2
def baseEnd_86653 : Nat := 9887697589812156319777

theorem tailTrace_86653 : CollatzResearch.WordTrace tailWord_86653 prefixEnd_86653 9887697589812156319777 := by
  unfold tailWord_86653
  simp only [CollatzResearch.WordTrace]
  refine ⟨3160494555078454999288613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2106996370052303332859075 3160494555078454999288613)
  ·
    refine ⟨592592729077210312366615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3160494555078454999288613 592592729077210312366615)
    ·
      refine ⟨888889093615815468549923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 592592729077210312366615 888889093615815468549923)
      ·
        refine ⟨1333333640423723202824885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 888889093615815468549923 1333333640423723202824885)
        ·
          refine ⟨125000028789724050264833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1333333640423723202824885 125000028789724050264833)
          ·
            refine ⟨93750021592293037698625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125000028789724050264833 93750021592293037698625)
            ·
              refine ⟨70312516194219778273969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93750021592293037698625 70312516194219778273969)
              ·
                refine ⟨52734387145664833705477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70312516194219778273969 52734387145664833705477)
                ·
                  refine ⟨9887697589812156319777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52734387145664833705477 9887697589812156319777)
                  ·
                    rfl

theorem cell22_86653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 2, 4].length) (baseStart_86653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_86653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_86653 prefixEnd_86653 := by exact prefixLift 86653
  have htrace : WordTrace (prefixWord ++ tailWord_86653) baseStart_86653 baseEnd_86653 := by
    simpa [prefixWord, tailWord_86653, baseEnd_86653] using wordTrace_append hprefix tailTrace_86653
  have hstable : (prefixWord ++ tailWord_86653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86653).length < 2 ^ (prefixWord ++ tailWord_86653).sum := by decide
  have hdescent : baseEnd_86653 < baseStart_86653 := by decide
  rcases family_descends (prefixWord ++ tailWord_86653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86679 : List Nat := [1, 1, 3, 3, 2, 1, 3, 2, 3, 3]
def baseStart_86679 : Nat := 118140960795 + 86679 * 2 ^ 59
def prefixEnd_86679 : Nat := 4983230072969 + 3 ^ 40 * 86679 * 2
def baseEnd_86679 : Nat := 29671993100781067809251

theorem tailTrace_86679 : CollatzResearch.WordTrace tailWord_86679 prefixEnd_86679 29671993100781067809251 := by
  unfold tailWord_86679
  simp only [CollatzResearch.WordTrace]
  refine ⟨3161442852984261439735091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2107628568656174293156727 3161442852984261439735091)
  ·
    refine ⟨4742164279476392159602637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3161442852984261439735091 4742164279476392159602637)
    ·
      refine ⟨1778311604803647059850989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4742164279476392159602637 1778311604803647059850989)
      ·
        refine ⟨666866851801367647444121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1778311604803647059850989 666866851801367647444121)
        ·
          refine ⟨500150138851025735583091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 666866851801367647444121 500150138851025735583091)
          ·
            refine ⟨750225208276538603374637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 500150138851025735583091 750225208276538603374637)
            ·
              refine ⟨281334453103701976265489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 750225208276538603374637 281334453103701976265489)
              ·
                refine ⟨211000839827776482199117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 281334453103701976265489 211000839827776482199117)
                ·
                  refine ⟨79125314935416180824669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 211000839827776482199117 79125314935416180824669)
                  ·
                    refine ⟨29671993100781067809251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79125314935416180824669 29671993100781067809251)
                    ·
                      rfl

theorem cell22_86679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 3, 3].length) (baseStart_86679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_86679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_86679 prefixEnd_86679 := by exact prefixLift 86679
  have htrace : WordTrace (prefixWord ++ tailWord_86679) baseStart_86679 baseEnd_86679 := by
    simpa [prefixWord, tailWord_86679, baseEnd_86679] using wordTrace_append hprefix tailTrace_86679
  have hstable : (prefixWord ++ tailWord_86679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86679).length < 2 ^ (prefixWord ++ tailWord_86679).sum := by decide
  have hdescent : baseEnd_86679 < baseStart_86679 := by decide
  rcases family_descends (prefixWord ++ tailWord_86679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86692 : List Nat := [2, 3, 1, 2, 2, 1, 2, 2, 7]
def baseStart_86692 : Nat := 118140960795 + 86692 * 2 ^ 59
def prefixEnd_86692 : Nat := 4983230072969 + 3 ^ 40 * 86692 * 2
def baseEnd_86692 : Nat := 9892147755484455744737

theorem tailTrace_86692 : CollatzResearch.WordTrace tailWord_86692 prefixEnd_86692 9892147755484455744737 := by
  unfold tailWord_86692
  simp only [CollatzResearch.WordTrace]
  refine ⟨1580958500968582329979165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2107944667958109773305553 1580958500968582329979165)
  ·
    refine ⟨592859437863218373742187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1580958500968582329979165 592859437863218373742187)
    ·
      refine ⟨889289156794827560613281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 592859437863218373742187 889289156794827560613281)
      ·
        refine ⟨666966867596120670459961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 889289156794827560613281 666966867596120670459961)
        ·
          refine ⟨500225150697090502844971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 666966867596120670459961 500225150697090502844971)
          ·
            refine ⟨750337726045635754267457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 500225150697090502844971 750337726045635754267457)
            ·
              refine ⟨562753294534226815700593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 750337726045635754267457 562753294534226815700593)
              ·
                refine ⟨422064970900670111775445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 562753294534226815700593 422064970900670111775445)
                ·
                  refine ⟨9892147755484455744737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 422064970900670111775445 9892147755484455744737)
                  ·
                    rfl

theorem cell22_86692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_86692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_86692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_86692 prefixEnd_86692 := by exact prefixLift 86692
  have htrace : WordTrace (prefixWord ++ tailWord_86692) baseStart_86692 baseEnd_86692 := by
    simpa [prefixWord, tailWord_86692, baseEnd_86692] using wordTrace_append hprefix tailTrace_86692
  have hstable : (prefixWord ++ tailWord_86692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86692).length < 2 ^ (prefixWord ++ tailWord_86692).sum := by decide
  have hdescent : baseEnd_86692 < baseStart_86692 := by decide
  rcases family_descends (prefixWord ++ tailWord_86692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86707 : List Nat := [1, 1, 1, 2, 3, 4, 1, 2, 2, 5]
def baseStart_86707 : Nat := 118140960795 + 86707 * 2 ^ 59
def prefixEnd_86707 : Nat := 4983230072969 + 3 ^ 40 * 86707 * 2
def baseEnd_86707 : Nat := 29681578072998328109165

theorem tailTrace_86707 : CollatzResearch.WordTrace tailWord_86707 prefixEnd_86707 29681578072998328109165 := by
  unfold tailWord_86707
  simp only [CollatzResearch.WordTrace]
  refine ⟨3162464096882822221754375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2108309397921881481169583 3162464096882822221754375)
  ·
    refine ⟨4743696145324233332631563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3162464096882822221754375 4743696145324233332631563)
    ·
      refine ⟨7115544217986349998947345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4743696145324233332631563 7115544217986349998947345)
      ·
        refine ⟨5336658163489762499210509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7115544217986349998947345 5336658163489762499210509)
        ·
          refine ⟨2001246811308660937203941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5336658163489762499210509 2001246811308660937203941)
          ·
            refine ⟨375233777120373925725739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2001246811308660937203941 375233777120373925725739)
            ·
              refine ⟨562850665680560888588609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 375233777120373925725739 562850665680560888588609)
              ·
                refine ⟨422137999260420666441457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 562850665680560888588609 422137999260420666441457)
                ·
                  refine ⟨316603499445315499831093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 422137999260420666441457 316603499445315499831093)
                  ·
                    refine ⟨29681578072998328109165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 316603499445315499831093 29681578072998328109165)
                    ·
                      rfl

theorem cell22_86707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 5].length) (baseStart_86707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_86707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_86707 prefixEnd_86707 := by exact prefixLift 86707
  have htrace : WordTrace (prefixWord ++ tailWord_86707) baseStart_86707 baseEnd_86707 := by
    simpa [prefixWord, tailWord_86707, baseEnd_86707] using wordTrace_append hprefix tailTrace_86707
  have hstable : (prefixWord ++ tailWord_86707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86707).length < 2 ^ (prefixWord ++ tailWord_86707).sum := by decide
  have hdescent : baseEnd_86707 < baseStart_86707 := by decide
  rcases family_descends (prefixWord ++ tailWord_86707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86709 : List Nat := [1, 3, 3, 3, 1, 2, 1, 1, 7]
def baseStart_86709 : Nat := 118140960795 + 86709 * 2 ^ 59
def prefixEnd_86709 : Nat := 4983230072969 + 3 ^ 40 * 86709 * 2
def baseEnd_86709 : Nat := 9894087571290329853053

theorem tailTrace_86709 : CollatzResearch.WordTrace tailWord_86709 prefixEnd_86709 9894087571290329853053 := by
  unfold tailWord_86709
  simp only [CollatzResearch.WordTrace]
  refine ⟨3162537042875576563327181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2108358028583717708884787 3162537042875576563327181)
  ·
    refine ⟨1185951391078341211247693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3162537042875576563327181 1185951391078341211247693)
    ·
      refine ⟨444731771654377954217885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1185951391078341211247693 444731771654377954217885)
      ·
        refine ⟨166774414370391732831707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 444731771654377954217885 166774414370391732831707)
        ·
          refine ⟨250161621555587599247561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166774414370391732831707 250161621555587599247561)
          ·
            refine ⟨187621216166690699435671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250161621555587599247561 187621216166690699435671)
            ·
              refine ⟨281431824250036049153507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187621216166690699435671 281431824250036049153507)
              ·
                refine ⟨422147736375054073730261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 281431824250036049153507 422147736375054073730261)
                ·
                  refine ⟨9894087571290329853053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 422147736375054073730261 9894087571290329853053)
                  ·
                    rfl

theorem cell22_86709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 7].length) (baseStart_86709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_86709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_86709 prefixEnd_86709 := by exact prefixLift 86709
  have htrace : WordTrace (prefixWord ++ tailWord_86709) baseStart_86709 baseEnd_86709 := by
    simpa [prefixWord, tailWord_86709, baseEnd_86709] using wordTrace_append hprefix tailTrace_86709
  have hstable : (prefixWord ++ tailWord_86709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86709).length < 2 ^ (prefixWord ++ tailWord_86709).sum := by decide
  have hdescent : baseEnd_86709 < baseStart_86709 := by decide
  rcases family_descends (prefixWord ++ tailWord_86709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86724 : List Nat := [2, 3, 3, 1, 1, 2, 2, 1, 2, 5]
def baseStart_86724 : Nat := 118140960795 + 86724 * 2 ^ 59
def prefixEnd_86724 : Nat := 4983230072969 + 3 ^ 40 * 86724 * 2
def baseEnd_86724 : Nat := 29687397520415950434113

theorem tailTrace_86724 : CollatzResearch.WordTrace tailWord_86724 prefixEnd_86724 29687397520415950434113 := by
  unfold tailWord_86724
  simp only [CollatzResearch.WordTrace]
  refine ⟨1581542068910617062561613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2108722758547489416748817 1581542068910617062561613)
  ·
    refine ⟨593078275841481398460605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1581542068910617062561613 593078275841481398460605)
    ·
      refine ⟨222404353440555524422727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 593078275841481398460605 222404353440555524422727)
      ·
        refine ⟨333606530160833286634091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222404353440555524422727 333606530160833286634091)
        ·
          refine ⟨500409795241249929951137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333606530160833286634091 500409795241249929951137)
          ·
            refine ⟨375307346430937447463353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 500409795241249929951137 375307346430937447463353)
            ·
              refine ⟨281480509823203085597515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 375307346430937447463353 281480509823203085597515)
              ·
                refine ⟨422220764734804628396273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 281480509823203085597515 422220764734804628396273)
                ·
                  refine ⟨316665573551103471297205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 422220764734804628396273 316665573551103471297205)
                  ·
                    refine ⟨29687397520415950434113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 316665573551103471297205 29687397520415950434113)
                    ·
                      rfl

theorem cell22_86724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_86724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_86724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_86724 prefixEnd_86724 := by exact prefixLift 86724
  have htrace : WordTrace (prefixWord ++ tailWord_86724) baseStart_86724 baseEnd_86724 := by
    simpa [prefixWord, tailWord_86724, baseEnd_86724] using wordTrace_append hprefix tailTrace_86724
  have hstable : (prefixWord ++ tailWord_86724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86724).length < 2 ^ (prefixWord ++ tailWord_86724).sum := by decide
  have hdescent : baseEnd_86724 < baseStart_86724 := by decide
  rcases family_descends (prefixWord ++ tailWord_86724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86737 : List Nat := [1, 2, 2, 1, 2, 3, 1, 4, 6]
def baseStart_86737 : Nat := 118140960795 + 86737 * 2 ^ 59
def prefixEnd_86737 : Nat := 4983230072969 + 3 ^ 40 * 86737 * 2
def baseEnd_86737 : Nat := 9897282562029416619691

theorem tailTrace_86737 : CollatzResearch.WordTrace tailWord_86737 prefixEnd_86737 9897282562029416619691 := by
  unfold tailWord_86737
  simp only [CollatzResearch.WordTrace]
  refine ⟨3163558286774137345346465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2109038857849424896897643 3163558286774137345346465)
  ·
    refine ⟨2372668715080603009009849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3163558286774137345346465 2372668715080603009009849)
    ·
      refine ⟨1779501536310452256757387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2372668715080603009009849 1779501536310452256757387)
      ·
        refine ⟨2669252304465678385136081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1779501536310452256757387 2669252304465678385136081)
        ·
          refine ⟨2001939228349258788852061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2669252304465678385136081 2001939228349258788852061)
          ·
            refine ⟨750727210630972045819523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2001939228349258788852061 750727210630972045819523)
            ·
              refine ⟨1126090815946458068729285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 750727210630972045819523 1126090815946458068729285)
              ·
                refine ⟨211142027989960887886741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1126090815946458068729285 211142027989960887886741)
                ·
                  refine ⟨9897282562029416619691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 211142027989960887886741 9897282562029416619691)
                  ·
                    rfl

theorem cell22_86737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 6].length) (baseStart_86737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_86737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_86737 prefixEnd_86737 := by exact prefixLift 86737
  have htrace : WordTrace (prefixWord ++ tailWord_86737) baseStart_86737 baseEnd_86737 := by
    simpa [prefixWord, tailWord_86737, baseEnd_86737] using wordTrace_append hprefix tailTrace_86737
  have hstable : (prefixWord ++ tailWord_86737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86737).length < 2 ^ (prefixWord ++ tailWord_86737).sum := by decide
  have hdescent : baseEnd_86737 < baseStart_86737 := by decide
  rcases family_descends (prefixWord ++ tailWord_86737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86752 : List Nat := [2, 1, 1, 3, 1, 2, 1, 3, 3, 5]
def baseStart_86752 : Nat := 118140960795 + 86752 * 2 ^ 59
def prefixEnd_86752 : Nat := 4983230072969 + 3 ^ 40 * 86752 * 2
def baseEnd_86752 : Nat := 29696982492633210734027

theorem tailTrace_86752 : CollatzResearch.WordTrace tailWord_86752 prefixEnd_86752 29696982492633210734027 := by
  unfold tailWord_86752
  simp only [CollatzResearch.WordTrace]
  refine ⟨1582052690859897453571255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2109403587813196604761673 1582052690859897453571255)
  ·
    refine ⟨2373079036289846180356883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1582052690859897453571255 2373079036289846180356883)
    ·
      refine ⟨3559618554434769270535325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2373079036289846180356883 3559618554434769270535325)
      ·
        refine ⟨1334856957913038476450747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3559618554434769270535325 1334856957913038476450747)
        ·
          refine ⟨2002285436869557714676121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1334856957913038476450747 2002285436869557714676121)
          ·
            refine ⟨1501714077652168286007091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2002285436869557714676121 1501714077652168286007091)
            ·
              refine ⟨2252571116478252429010637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1501714077652168286007091 2252571116478252429010637)
              ·
                refine ⟨844714168679344660878989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2252571116478252429010637 844714168679344660878989)
                ·
                  refine ⟨316767813254754247829621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 844714168679344660878989 316767813254754247829621)
                  ·
                    refine ⟨29696982492633210734027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 316767813254754247829621 29696982492633210734027)
                    ·
                      rfl

theorem cell22_86752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 3, 5].length) (baseStart_86752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_86752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_86752 prefixEnd_86752 := by exact prefixLift 86752
  have htrace : WordTrace (prefixWord ++ tailWord_86752) baseStart_86752 baseEnd_86752 := by
    simpa [prefixWord, tailWord_86752, baseEnd_86752] using wordTrace_append hprefix tailTrace_86752
  have hstable : (prefixWord ++ tailWord_86752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86752).length < 2 ^ (prefixWord ++ tailWord_86752).sum := by decide
  have hdescent : baseEnd_86752 < baseStart_86752 := by decide
  rcases family_descends (prefixWord ++ tailWord_86752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86769 : List Nat := [1, 2, 2, 2, 2, 2, 1, 3, 4, 3]
def baseStart_86769 : Nat := 118140960795 + 86769 * 2 ^ 59
def prefixEnd_86769 : Nat := 4983230072969 + 3 ^ 40 * 86769 * 2
def baseEnd_86769 : Nat := 29702801940050833058975

theorem tailTrace_86769 : CollatzResearch.WordTrace tailWord_86769 prefixEnd_86769 29702801940050833058975 := by
  unfold tailWord_86769
  simp only [CollatzResearch.WordTrace]
  refine ⟨3164725422658206810511361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2109816948438804540340907 3164725422658206810511361)
  ·
    refine ⟨2373544066993655107883521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3164725422658206810511361 2373544066993655107883521)
    ·
      refine ⟨1780158050245241330912641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2373544066993655107883521 1780158050245241330912641)
      ·
        refine ⟨1335118537683930998184481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1780158050245241330912641 1335118537683930998184481)
        ·
          refine ⟨1001338903262948248638361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1335118537683930998184481 1001338903262948248638361)
          ·
            refine ⟨751004177447211186478771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1001338903262948248638361 751004177447211186478771)
            ·
              refine ⟨1126506266170816779718157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 751004177447211186478771 1126506266170816779718157)
              ·
                refine ⟨422439849814056292394309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1126506266170816779718157 422439849814056292394309)
                ·
                  refine ⟨79207471840135554823933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 422439849814056292394309 79207471840135554823933)
                  ·
                    refine ⟨29702801940050833058975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79207471840135554823933 29702801940050833058975)
                    ·
                      rfl

theorem cell22_86769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 4, 3].length) (baseStart_86769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_86769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_86769 prefixEnd_86769 := by exact prefixLift 86769
  have htrace : WordTrace (prefixWord ++ tailWord_86769) baseStart_86769 baseEnd_86769 := by
    simpa [prefixWord, tailWord_86769, baseEnd_86769] using wordTrace_append hprefix tailTrace_86769
  have hstable : (prefixWord ++ tailWord_86769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86769).length < 2 ^ (prefixWord ++ tailWord_86769).sum := by decide
  have hdescent : baseEnd_86769 < baseStart_86769 := by decide
  rcases family_descends (prefixWord ++ tailWord_86769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86852 : List Nat := [2, 3, 4, 2, 2, 1, 1, 1, 2, 4]
def baseStart_86852 : Nat := 118140960795 + 86852 * 2 ^ 59
def prefixEnd_86852 : Nat := 4983230072969 + 3 ^ 40 * 86852 * 2
def baseEnd_86852 : Nat := 29731214536266283233721

theorem tailTrace_86852 : CollatzResearch.WordTrace tailWord_86852 prefixEnd_86852 29731214536266283233721 := by
  unfold tailWord_86852
  simp only [CollatzResearch.WordTrace]
  refine ⟨1583876340678755992891405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2111835120905007990521873 1583876340678755992891405)
  ·
    refine ⟨593953627754533497334277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1583876340678755992891405 593953627754533497334277)
    ·
      refine ⟨111366305203975030750177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 593953627754533497334277 111366305203975030750177)
      ·
        refine ⟨83524728902981273062633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111366305203975030750177 83524728902981273062633)
        ·
          refine ⟨62643546677235954796975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83524728902981273062633 62643546677235954796975)
          ·
            refine ⟨93965320015853932195463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62643546677235954796975 93965320015853932195463)
            ·
              refine ⟨140947980023780898293195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93965320015853932195463 140947980023780898293195)
              ·
                refine ⟨211421970035671347439793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140947980023780898293195 211421970035671347439793)
                ·
                  refine ⟨158566477526753510579845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 211421970035671347439793 158566477526753510579845)
                  ·
                    refine ⟨29731214536266283233721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 158566477526753510579845 29731214536266283233721)
                    ·
                      rfl

theorem cell22_86852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_86852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_86852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_86852 prefixEnd_86852 := by exact prefixLift 86852
  have htrace : WordTrace (prefixWord ++ tailWord_86852) baseStart_86852 baseEnd_86852 := by
    simpa [prefixWord, tailWord_86852, baseEnd_86852] using wordTrace_append hprefix tailTrace_86852
  have hstable : (prefixWord ++ tailWord_86852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86852).length < 2 ^ (prefixWord ++ tailWord_86852).sum := by decide
  have hdescent : baseEnd_86852 < baseStart_86852 := by decide
  rcases family_descends (prefixWord ++ tailWord_86852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86865 : List Nat := [1, 2, 2, 1, 6, 1, 2, 3, 1, 3]
def baseStart_86865 : Nat := 118140960795 + 86865 * 2 ^ 59
def prefixEnd_86865 : Nat := 4983230072969 + 3 ^ 40 * 86865 * 2
def baseEnd_86865 : Nat := 29735664701938582658681

theorem tailTrace_86865 : CollatzResearch.WordTrace tailWord_86865 prefixEnd_86865 29735664701938582658681 := by
  unfold tailWord_86865
  simp only [CollatzResearch.WordTrace]
  refine ⟨3168226830310415206006049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2112151220206943470670699 3168226830310415206006049)
  ·
    refine ⟨2376170122732811404504537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3168226830310415206006049 2376170122732811404504537)
    ·
      refine ⟨1782127592049608553378403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2376170122732811404504537 1782127592049608553378403)
      ·
        refine ⟨2673191388074412830067605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1782127592049608553378403 2673191388074412830067605)
        ·
          refine ⟨125305846315988101409419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2673191388074412830067605 125305846315988101409419)
          ·
            refine ⟨187958769473982152114129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125305846315988101409419 187958769473982152114129)
            ·
              refine ⟨140969077105486614085597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187958769473982152114129 140969077105486614085597)
              ·
                refine ⟨52863403914557480282099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140969077105486614085597 52863403914557480282099)
                ·
                  refine ⟨79295105871836220423149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52863403914557480282099 79295105871836220423149)
                  ·
                    refine ⟨29735664701938582658681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79295105871836220423149 29735664701938582658681)
                    ·
                      rfl

theorem cell22_86865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 3, 1, 3].length) (baseStart_86865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_86865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_86865 prefixEnd_86865 := by exact prefixLift 86865
  have htrace : WordTrace (prefixWord ++ tailWord_86865) baseStart_86865 baseEnd_86865 := by
    simpa [prefixWord, tailWord_86865, baseEnd_86865] using wordTrace_append hprefix tailTrace_86865
  have hstable : (prefixWord ++ tailWord_86865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86865).length < 2 ^ (prefixWord ++ tailWord_86865).sum := by decide
  have hdescent : baseEnd_86865 < baseStart_86865 := by decide
  rcases family_descends (prefixWord ++ tailWord_86865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86876 : List Nat := [2, 2, 4, 2, 1, 1, 1, 2, 2, 5]
def baseStart_86876 : Nat := 118140960795 + 86876 * 2 ^ 59
def prefixEnd_86876 : Nat := 4983230072969 + 3 ^ 40 * 86876 * 2
def baseEnd_86876 : Nat := 29739430226738220633647

theorem tailTrace_86876 : CollatzResearch.WordTrace tailWord_86876 prefixEnd_86876 29739430226738220633647 := by
  unfold tailWord_86876
  simp only [CollatzResearch.WordTrace]
  refine ⟨1584314016635282042328241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2112418688847042723104321 1584314016635282042328241)
  ·
    refine ⟨1188235512476461531746181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1584314016635282042328241 1188235512476461531746181)
    ·
      refine ⟨222794158589336537202409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1188235512476461531746181 222794158589336537202409)
      ·
        refine ⟨167095618942002402901807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222794158589336537202409 167095618942002402901807)
        ·
          refine ⟨250643428413003604352711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167095618942002402901807 250643428413003604352711)
          ·
            refine ⟨375965142619505406529067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250643428413003604352711 375965142619505406529067)
            ·
              refine ⟨563947713929258109793601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 375965142619505406529067 563947713929258109793601)
              ·
                refine ⟨422960785446943582345201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 563947713929258109793601 422960785446943582345201)
                ·
                  refine ⟨317220589085207686758901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 422960785446943582345201 317220589085207686758901)
                  ·
                    refine ⟨29739430226738220633647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 317220589085207686758901 29739430226738220633647)
                    ·
                      rfl

theorem cell22_86876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_86876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_86876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_86876 prefixEnd_86876 := by exact prefixLift 86876
  have htrace : WordTrace (prefixWord ++ tailWord_86876) baseStart_86876 baseEnd_86876 := by
    simpa [prefixWord, tailWord_86876, baseEnd_86876] using wordTrace_append hprefix tailTrace_86876
  have hstable : (prefixWord ++ tailWord_86876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86876).length < 2 ^ (prefixWord ++ tailWord_86876).sum := by decide
  have hdescent : baseEnd_86876 < baseStart_86876 := by decide
  rcases family_descends (prefixWord ++ tailWord_86876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86904 : List Nat := [2, 1, 2, 1, 1, 1, 1, 7, 1, 5]
def baseStart_86904 : Nat := 118140960795 + 86904 * 2 ^ 59
def prefixEnd_86904 : Nat := 4983230072969 + 3 ^ 40 * 86904 * 2
def baseEnd_86904 : Nat := 29749015198955480933561

theorem tailTrace_86904 : CollatzResearch.WordTrace tailWord_86904 prefixEnd_86904 29749015198955480933561 := by
  unfold tailWord_86904
  simp only [CollatzResearch.WordTrace]
  refine ⟨1584824638584562433337883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2113099518112749911117177 1584824638584562433337883)
  ·
    refine ⟨2377236957876843650006825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1584824638584562433337883 2377236957876843650006825)
    ·
      refine ⟨1782927718407632737505119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2377236957876843650006825 1782927718407632737505119)
      ·
        refine ⟨2674391577611449106257679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1782927718407632737505119 2674391577611449106257679)
        ·
          refine ⟨4011587366417173659386519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2674391577611449106257679 4011587366417173659386519)
          ·
            refine ⟨6017381049625760489079779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4011587366417173659386519 6017381049625760489079779)
            ·
              refine ⟨9026071574438640733619669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6017381049625760489079779 9026071574438640733619669)
              ·
                refine ⟨211548552525905642194211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 9026071574438640733619669 211548552525905642194211)
                ·
                  refine ⟨317322828788858463291317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 211548552525905642194211 317322828788858463291317)
                  ·
                    refine ⟨29749015198955480933561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 317322828788858463291317 29749015198955480933561)
                    ·
                      rfl

theorem cell22_86904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 1, 5].length) (baseStart_86904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_86904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_86904 prefixEnd_86904 := by exact prefixLift 86904
  have htrace : WordTrace (prefixWord ++ tailWord_86904) baseStart_86904 baseEnd_86904 := by
    simpa [prefixWord, tailWord_86904, baseEnd_86904] using wordTrace_append hprefix tailTrace_86904
  have hstable : (prefixWord ++ tailWord_86904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86904).length < 2 ^ (prefixWord ++ tailWord_86904).sum := by decide
  have hdescent : baseEnd_86904 < baseStart_86904 := by decide
  rcases family_descends (prefixWord ++ tailWord_86904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86921 : List Nat := [1, 2, 1, 1, 5, 2, 1, 2, 4, 3]
def baseStart_86921 : Nat := 118140960795 + 86921 * 2 ^ 59
def prefixEnd_86921 : Nat := 4983230072969 + 3 ^ 40 * 86921 * 2
def baseEnd_86921 : Nat := 29754834646373103258509

theorem tailTrace_86921 : CollatzResearch.WordTrace tailWord_86921 prefixEnd_86921 29754834646373103258509 := by
  unfold tailWord_86921
  simp only [CollatzResearch.WordTrace]
  refine ⟨3170269318107536770044617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2113512878738357846696411 3170269318107536770044617)
  ·
    refine ⟨2377701988580652577533463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3170269318107536770044617 2377701988580652577533463)
    ·
      refine ⟨3566552982870978866300195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2377701988580652577533463 3566552982870978866300195)
      ·
        refine ⟨5349829474306468299450293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3566552982870978866300195 5349829474306468299450293)
        ·
          refine ⟨501546513216231403073465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5349829474306468299450293 501546513216231403073465)
          ·
            refine ⟨376159884912173552305099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 501546513216231403073465 376159884912173552305099)
            ·
              refine ⟨564239827368260328457649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 376159884912173552305099 564239827368260328457649)
              ·
                refine ⟨423179870526195246343237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 564239827368260328457649 423179870526195246343237)
                ·
                  refine ⟨79346225723661608689357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 423179870526195246343237 79346225723661608689357)
                  ·
                    refine ⟨29754834646373103258509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79346225723661608689357 29754834646373103258509)
                    ·
                      rfl

theorem cell22_86921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 4, 3].length) (baseStart_86921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_86921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_86921 prefixEnd_86921 := by exact prefixLift 86921
  have htrace : WordTrace (prefixWord ++ tailWord_86921) baseStart_86921 baseEnd_86921 := by
    simpa [prefixWord, tailWord_86921, baseEnd_86921] using wordTrace_append hprefix tailTrace_86921
  have hstable : (prefixWord ++ tailWord_86921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86921).length < 2 ^ (prefixWord ++ tailWord_86921).sum := by decide
  have hdescent : baseEnd_86921 < baseStart_86921 := by decide
  rcases family_descends (prefixWord ++ tailWord_86921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86940 : List Nat := [2, 2, 3, 3, 3, 1, 1, 1, 6]
def baseStart_86940 : Nat := 118140960795 + 86940 * 2 ^ 59
def prefixEnd_86940 : Nat := 4983230072969 + 3 ^ 40 * 86940 * 2
def baseEnd_86940 : Nat := 9920446244887795677817

theorem tailTrace_86940 : CollatzResearch.WordTrace tailWord_86940 prefixEnd_86940 9920446244887795677817 := by
  unfold tailWord_86940
  simp only [CollatzResearch.WordTrace]
  refine ⟨1585481152519351507493137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2113974870025802009990849 1585481152519351507493137)
  ·
    refine ⟨1189110864389513630619853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1585481152519351507493137 1189110864389513630619853)
    ·
      refine ⟨445916574146067611482445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1189110864389513630619853 445916574146067611482445)
      ·
        refine ⟨167218715304775354305917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 445916574146067611482445 167218715304775354305917)
        ·
          refine ⟨62707018239290757864719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167218715304775354305917 62707018239290757864719)
          ·
            refine ⟨94060527358936136797079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62707018239290757864719 94060527358936136797079)
            ·
              refine ⟨141090791038404205195619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94060527358936136797079 141090791038404205195619)
              ·
                refine ⟨211636186557606307793429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141090791038404205195619 211636186557606307793429)
                ·
                  refine ⟨9920446244887795677817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 211636186557606307793429 9920446244887795677817)
                  ·
                    rfl

theorem cell22_86940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 6].length) (baseStart_86940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_86940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_86940 prefixEnd_86940 := by exact prefixLift 86940
  have htrace : WordTrace (prefixWord ++ tailWord_86940) baseStart_86940 baseEnd_86940 := by
    simpa [prefixWord, tailWord_86940, baseEnd_86940] using wordTrace_append hprefix tailTrace_86940
  have hstable : (prefixWord ++ tailWord_86940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86940).length < 2 ^ (prefixWord ++ tailWord_86940).sum := by decide
  have hdescent : baseEnd_86940 < baseStart_86940 := by decide
  rcases family_descends (prefixWord ++ tailWord_86940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86998 : List Nat := [5, 2, 1, 1, 2, 1, 1, 1, 2, 6]
def baseStart_86998 : Nat := 118140960795 + 86998 * 2 ^ 59
def prefixEnd_86998 : Nat := 4983230072969 + 3 ^ 40 * 86998 * 2
def baseEnd_86998 : Nat := 29781193319970569083273

theorem tailTrace_86998 : CollatzResearch.WordTrace tailWord_86998 prefixEnd_86998 29781193319970569083273 := by
  unfold tailWord_86998
  simp only [CollatzResearch.WordTrace]
  refine ⟨198317358676786182537353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2115385159219052613731765 198317358676786182537353)
  ·
    refine ⟨148738019007589636903015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198317358676786182537353 148738019007589636903015)
    ·
      refine ⟨223107028511384455354523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148738019007589636903015 223107028511384455354523)
      ·
        refine ⟨334660542767076683031785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223107028511384455354523 334660542767076683031785)
        ·
          refine ⟨250995407075307512273839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 334660542767076683031785 250995407075307512273839)
          ·
            refine ⟨376493110612961268410759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250995407075307512273839 376493110612961268410759)
            ·
              refine ⟨564739665919441902616139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 376493110612961268410759 564739665919441902616139)
              ·
                refine ⟨847109498879162853924209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 564739665919441902616139 847109498879162853924209)
                ·
                  refine ⟨635332124159372140443157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 847109498879162853924209 635332124159372140443157)
                  ·
                    refine ⟨29781193319970569083273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 635332124159372140443157 29781193319970569083273)
                    ·
                      rfl

theorem cell22_86998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_86998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_86998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_86998 prefixEnd_86998 := by exact prefixLift 86998
  have htrace : WordTrace (prefixWord ++ tailWord_86998) baseStart_86998 baseEnd_86998 := by
    simpa [prefixWord, tailWord_86998, baseEnd_86998] using wordTrace_append hprefix tailTrace_86998
  have hstable : (prefixWord ++ tailWord_86998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86998).length < 2 ^ (prefixWord ++ tailWord_86998).sum := by decide
  have hdescent : baseEnd_86998 < baseStart_86998 := by decide
  rcases family_descends (prefixWord ++ tailWord_86998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87000 : List Nat := [2, 1, 2, 2, 2, 4, 1, 4, 1, 3]
def baseStart_87000 : Nat := 118140960795 + 87000 * 2 ^ 59
def prefixEnd_87000 : Nat := 4983230072969 + 3 ^ 40 * 87000 * 2
def baseEnd_87000 : Nat := 29781877960843230533267

theorem tailTrace_87000 : CollatzResearch.WordTrace tailWord_87000 prefixEnd_87000 29781877960843230533267 := by
  unfold tailWord_87000
  simp only [CollatzResearch.WordTrace]
  refine ⟨1586575342410666631085227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2115433789880888841446969 1586575342410666631085227)
  ·
    refine ⟨2379863013615999946627841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1586575342410666631085227 2379863013615999946627841)
    ·
      refine ⟨1784897260211999959970881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2379863013615999946627841 1784897260211999959970881)
      ·
        refine ⟨1338672945158999969978161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1784897260211999959970881 1338672945158999969978161)
        ·
          refine ⟨1004004708869249977483621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1338672945158999969978161 1004004708869249977483621)
          ·
            refine ⟨188250882912984370778179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1004004708869249977483621 188250882912984370778179)
            ·
              refine ⟨282376324369476556167269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188250882912984370778179 282376324369476556167269)
              ·
                refine ⟨52945560819276854281363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 282376324369476556167269 52945560819276854281363)
                ·
                  refine ⟨79418341228915281422045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52945560819276854281363 79418341228915281422045)
                  ·
                    refine ⟨29781877960843230533267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79418341228915281422045 29781877960843230533267)
                    ·
                      rfl

theorem cell22_87000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 4, 1, 3].length) (baseStart_87000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87000 prefixEnd_87000 := by exact prefixLift 87000
  have htrace : WordTrace (prefixWord ++ tailWord_87000) baseStart_87000 baseEnd_87000 := by
    simpa [prefixWord, tailWord_87000, baseEnd_87000] using wordTrace_append hprefix tailTrace_87000
  have hstable : (prefixWord ++ tailWord_87000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87000).length < 2 ^ (prefixWord ++ tailWord_87000).sum := by decide
  have hdescent : baseEnd_87000 < baseStart_87000 := by decide
  rcases family_descends (prefixWord ++ tailWord_87000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87011 : List Nat := [1, 1, 1, 6, 1, 1, 3, 1, 2, 5]
def baseStart_87011 : Nat := 118140960795 + 87011 * 2 ^ 59
def prefixEnd_87011 : Nat := 4983230072969 + 3 ^ 40 * 87011 * 2
def baseEnd_87011 : Nat := 29785643485642868508233

theorem tailTrace_87011 : CollatzResearch.WordTrace tailWord_87011 prefixEnd_87011 29785643485642868508233 := by
  unfold tailWord_87011
  simp only [CollatzResearch.WordTrace]
  refine ⟨3173551887781482140820887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2115701258520988093880591 3173551887781482140820887)
  ·
    refine ⟨4760327831672223211231331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3173551887781482140820887 4760327831672223211231331)
    ·
      refine ⟨7140491747508334816846997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4760327831672223211231331 7140491747508334816846997)
      ·
        refine ⟨334710550664453194539703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7140491747508334816846997 334710550664453194539703)
        ·
          refine ⟨502065825996679791809555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334710550664453194539703 502065825996679791809555)
          ·
            refine ⟨753098738995019687714333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502065825996679791809555 753098738995019687714333)
            ·
              refine ⟨282412027123132382892875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 753098738995019687714333 282412027123132382892875)
              ·
                refine ⟨423618040684698574339313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 282412027123132382892875 423618040684698574339313)
                ·
                  refine ⟨317713530513523930754485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 423618040684698574339313 317713530513523930754485)
                  ·
                    refine ⟨29785643485642868508233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 317713530513523930754485 29785643485642868508233)
                    ·
                      rfl

theorem cell22_87011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 5].length) (baseStart_87011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87011 prefixEnd_87011 := by exact prefixLift 87011
  have htrace : WordTrace (prefixWord ++ tailWord_87011) baseStart_87011 baseEnd_87011 := by
    simpa [prefixWord, tailWord_87011, baseEnd_87011] using wordTrace_append hprefix tailTrace_87011
  have hstable : (prefixWord ++ tailWord_87011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87011).length < 2 ^ (prefixWord ++ tailWord_87011).sum := by decide
  have hdescent : baseEnd_87011 < baseStart_87011 := by decide
  rcases family_descends (prefixWord ++ tailWord_87011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87071 : List Nat := [1, 1, 2, 4, 1, 3, 1, 2, 1, 6]
def baseStart_87071 : Nat := 118140960795 + 87071 * 2 ^ 59
def prefixEnd_87071 : Nat := 4983230072969 + 3 ^ 40 * 87071 * 2
def baseEnd_87071 : Nat := 29806182711822712008049

theorem tailTrace_87071 : CollatzResearch.WordTrace tailWord_87071 prefixEnd_87071 29806182711822712008049 := by
  unfold tailWord_87071
  simp only [CollatzResearch.WordTrace]
  refine ⟨3175740267564112388005067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2117160178376074925336711 3175740267564112388005067)
  ·
    refine ⟨4763610401346168582007601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3175740267564112388005067 4763610401346168582007601)
    ·
      refine ⟨3572707801009626436505701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4763610401346168582007601 3572707801009626436505701)
      ·
        refine ⟨669882712689304956844819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3572707801009626436505701 669882712689304956844819)
        ·
          refine ⟨1004824069033957435267229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 669882712689304956844819 1004824069033957435267229)
          ·
            refine ⟨376809025887734038225211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1004824069033957435267229 376809025887734038225211)
            ·
              refine ⟨565213538831601057337817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 376809025887734038225211 565213538831601057337817)
              ·
                refine ⟨423910154123700793003363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 565213538831601057337817 423910154123700793003363)
                ·
                  refine ⟨635865231185551189505045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 423910154123700793003363 635865231185551189505045)
                  ·
                    refine ⟨29806182711822712008049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 635865231185551189505045 29806182711822712008049)
                    ·
                      rfl

theorem cell22_87071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 6].length) (baseStart_87071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87071 prefixEnd_87071 := by exact prefixLift 87071
  have htrace : WordTrace (prefixWord ++ tailWord_87071) baseStart_87071 baseEnd_87071 := by
    simpa [prefixWord, tailWord_87071, baseEnd_87071] using wordTrace_append hprefix tailTrace_87071
  have hstable : (prefixWord ++ tailWord_87071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87071).length < 2 ^ (prefixWord ++ tailWord_87071).sum := by decide
  have hdescent : baseEnd_87071 < baseStart_87071 := by decide
  rcases family_descends (prefixWord ++ tailWord_87071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87073 : List Nat := [1, 2, 3, 2, 3, 1, 3, 1, 1, 5]
def baseStart_87073 : Nat := 118140960795 + 87073 * 2 ^ 59
def prefixEnd_87073 : Nat := 4983230072969 + 3 ^ 40 * 87073 * 2
def baseEnd_87073 : Nat := 29806867352695373458043

theorem tailTrace_87073 : CollatzResearch.WordTrace tailWord_87073 prefixEnd_87073 29806867352695373458043 := by
  unfold tailWord_87073
  simp only [CollatzResearch.WordTrace]
  refine ⟨3175813213556866729577873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2117208809037911153051915 3175813213556866729577873)
  ·
    refine ⟨2381859910167650047183405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3175813213556866729577873 2381859910167650047183405)
    ·
      refine ⟨893197466312868767693777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2381859910167650047183405 893197466312868767693777)
      ·
        refine ⟨669898099734651575770333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 893197466312868767693777 669898099734651575770333)
        ·
          refine ⟨251211787400494340913875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 669898099734651575770333 251211787400494340913875)
          ·
            refine ⟨376817681100741511370813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251211787400494340913875 376817681100741511370813)
            ·
              refine ⟨141306630412778066764055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 376817681100741511370813 141306630412778066764055)
              ·
                refine ⟨211959945619167100146083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141306630412778066764055 211959945619167100146083)
                ·
                  refine ⟨317939918428750650219125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 211959945619167100146083 317939918428750650219125)
                  ·
                    refine ⟨29806867352695373458043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 317939918428750650219125 29806867352695373458043)
                    ·
                      rfl

theorem cell22_87073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_87073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87073 prefixEnd_87073 := by exact prefixLift 87073
  have htrace : WordTrace (prefixWord ++ tailWord_87073) baseStart_87073 baseEnd_87073 := by
    simpa [prefixWord, tailWord_87073, baseEnd_87073] using wordTrace_append hprefix tailTrace_87073
  have hstable : (prefixWord ++ tailWord_87073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87073).length < 2 ^ (prefixWord ++ tailWord_87073).sum := by decide
  have hdescent : baseEnd_87073 < baseStart_87073 := by decide
  rcases family_descends (prefixWord ++ tailWord_87073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87092 : List Nat := [2, 5, 1, 2, 1, 1, 3, 3, 4]
def baseStart_87092 : Nat := 118140960795 + 87092 * 2 ^ 59
def prefixEnd_87092 : Nat := 4983230072969 + 3 ^ 40 * 87092 * 2
def baseEnd_87092 : Nat := 9937790480328552410995

theorem tailTrace_87092 : CollatzResearch.WordTrace tailWord_87092 prefixEnd_87092 9937790480328552410995 := by
  unfold tailWord_87092
  simp only [CollatzResearch.WordTrace]
  refine ⟨1588253100244016487259765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2117670800325355316346353 1588253100244016487259765)
  ·
    refine ⟨148898728147876545680603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1588253100244016487259765 148898728147876545680603)
    ·
      refine ⟨223348092221814818520905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148898728147876545680603 223348092221814818520905)
      ·
        refine ⟨167511069166361113890679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223348092221814818520905 167511069166361113890679)
        ·
          refine ⟨251266603749541670836019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167511069166361113890679 251266603749541670836019)
          ·
            refine ⟨376899905624312506254029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251266603749541670836019 376899905624312506254029)
            ·
              refine ⟨141337464609117189845261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 376899905624312506254029 141337464609117189845261)
              ·
                refine ⟨53001549228418946191973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141337464609117189845261 53001549228418946191973)
                ·
                  refine ⟨9937790480328552410995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53001549228418946191973 9937790480328552410995)
                  ·
                    rfl

theorem cell22_87092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_87092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87092 prefixEnd_87092 := by exact prefixLift 87092
  have htrace : WordTrace (prefixWord ++ tailWord_87092) baseStart_87092 baseEnd_87092 := by
    simpa [prefixWord, tailWord_87092, baseEnd_87092] using wordTrace_append hprefix tailTrace_87092
  have hstable : (prefixWord ++ tailWord_87092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87092).length < 2 ^ (prefixWord ++ tailWord_87092).sum := by decide
  have hdescent : baseEnd_87092 < baseStart_87092 := by decide
  rcases family_descends (prefixWord ++ tailWord_87092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87105 : List Nat := [1, 2, 5, 1, 3, 1, 1, 2, 2, 4]
def baseStart_87105 : Nat := 118140960795 + 87105 * 2 ^ 59
def prefixEnd_87105 : Nat := 4983230072969 + 3 ^ 40 * 87105 * 2
def baseEnd_87105 : Nat := 29817821606657956657945

theorem tailTrace_87105 : CollatzResearch.WordTrace tailWord_87105 prefixEnd_87105 29817821606657956657945 := by
  unfold tailWord_87105
  simp only [CollatzResearch.WordTrace]
  refine ⟨3176980349440936194742769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2117986899627290796495179 3176980349440936194742769)
  ·
    refine ⟨2382735262080702146057077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3176980349440936194742769 2382735262080702146057077)
    ·
      refine ⟨223381430820065826192851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2382735262080702146057077 223381430820065826192851)
      ·
        refine ⟨335072146230098739289277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223381430820065826192851 335072146230098739289277)
        ·
          refine ⟨125652054836287027233479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 335072146230098739289277 125652054836287027233479)
          ·
            refine ⟨188478082254430540850219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125652054836287027233479 188478082254430540850219)
            ·
              refine ⟨282717123381645811275329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188478082254430540850219 282717123381645811275329)
              ·
                refine ⟨212037842536234358456497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 282717123381645811275329 212037842536234358456497)
                ·
                  refine ⟨159028381902175768842373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 212037842536234358456497 159028381902175768842373)
                  ·
                    refine ⟨29817821606657956657945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 159028381902175768842373 29817821606657956657945)
                    ·
                      rfl

theorem cell22_87105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_87105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87105 prefixEnd_87105 := by exact prefixLift 87105
  have htrace : WordTrace (prefixWord ++ tailWord_87105) baseStart_87105 baseEnd_87105 := by
    simpa [prefixWord, tailWord_87105, baseEnd_87105] using wordTrace_append hprefix tailTrace_87105
  have hstable : (prefixWord ++ tailWord_87105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87105).length < 2 ^ (prefixWord ++ tailWord_87105).sum := by decide
  have hdescent : baseEnd_87105 < baseStart_87105 := by decide
  rcases family_descends (prefixWord ++ tailWord_87105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87116 : List Nat := [2, 2, 1, 3, 1, 1, 1, 3, 2, 6]
def baseStart_87116 : Nat := 118140960795 + 87116 * 2 ^ 59
def prefixEnd_87116 : Nat := 4983230072969 + 3 ^ 40 * 87116 * 2
def baseEnd_87116 : Nat := 29821587131457594632911

theorem tailTrace_87116 : CollatzResearch.WordTrace tailWord_87116 prefixEnd_87116 29821587131457594632911 := by
  unfold tailWord_87116
  simp only [CollatzResearch.WordTrace]
  refine ⟨1588690776200542536696601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2118254368267390048928801 1588690776200542536696601)
  ·
    refine ⟨1191518082150406902522451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1588690776200542536696601 1191518082150406902522451)
    ·
      refine ⟨1787277123225610353783677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1191518082150406902522451 1787277123225610353783677)
      ·
        refine ⟨670228921209603882668879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1787277123225610353783677 670228921209603882668879)
        ·
          refine ⟨1005343381814405824003319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 670228921209603882668879 1005343381814405824003319)
          ·
            refine ⟨1508015072721608736004979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1005343381814405824003319 1508015072721608736004979)
            ·
              refine ⟨2262022609082413104007469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1508015072721608736004979 2262022609082413104007469)
              ·
                refine ⟨848258478405904914002801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2262022609082413104007469 848258478405904914002801)
                ·
                  refine ⟨636193858804428685502101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 848258478405904914002801 636193858804428685502101)
                  ·
                    refine ⟨29821587131457594632911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 636193858804428685502101 29821587131457594632911)
                    ·
                      rfl

theorem cell22_87116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_87116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87116 prefixEnd_87116 := by exact prefixLift 87116
  have htrace : WordTrace (prefixWord ++ tailWord_87116) baseStart_87116 baseEnd_87116 := by
    simpa [prefixWord, tailWord_87116, baseEnd_87116] using wordTrace_append hprefix tailTrace_87116
  have hstable : (prefixWord ++ tailWord_87116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87116).length < 2 ^ (prefixWord ++ tailWord_87116).sum := by decide
  have hdescent : baseEnd_87116 < baseStart_87116 := by decide
  rcases family_descends (prefixWord ++ tailWord_87116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87169 : List Nat := [1, 2, 4, 2, 2, 1, 4, 2, 1, 3]
def baseStart_87169 : Nat := 118140960795 + 87169 * 2 ^ 59
def prefixEnd_87169 : Nat := 4983230072969 + 3 ^ 40 * 87169 * 2
def baseEnd_87169 : Nat := 29839730114583123057749

theorem tailTrace_87169 : CollatzResearch.WordTrace tailWord_87169 prefixEnd_87169 29839730114583123057749 := by
  unfold tailWord_87169
  simp only [CollatzResearch.WordTrace]
  refine ⟨3179314621209075125072561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2119543080806050083381707 3179314621209075125072561)
  ·
    refine ⟨2384485965906806343804421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3179314621209075125072561 2384485965906806343804421)
    ·
      refine ⟨447091118607526189463329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2384485965906806343804421 447091118607526189463329)
      ·
        refine ⟨335318338955644642097497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 447091118607526189463329 335318338955644642097497)
        ·
          refine ⟨251488754216733481573123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 335318338955644642097497 251488754216733481573123)
          ·
            refine ⟨377233131325100222359685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251488754216733481573123 377233131325100222359685)
            ·
              refine ⟨70731212123456291692441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 377233131325100222359685 70731212123456291692441)
              ·
                refine ⟨53048409092592218769331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70731212123456291692441 53048409092592218769331)
                ·
                  refine ⟨79572613638888328153997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53048409092592218769331 79572613638888328153997)
                  ·
                    refine ⟨29839730114583123057749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79572613638888328153997 29839730114583123057749)
                    ·
                      rfl

theorem cell22_87169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_87169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87169 prefixEnd_87169 := by exact prefixLift 87169
  have htrace : WordTrace (prefixWord ++ tailWord_87169) baseStart_87169 baseEnd_87169 := by
    simpa [prefixWord, tailWord_87169, baseEnd_87169] using wordTrace_append hprefix tailTrace_87169
  have hstable : (prefixWord ++ tailWord_87169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87169).length < 2 ^ (prefixWord ++ tailWord_87169).sum := by decide
  have hdescent : baseEnd_87169 < baseStart_87169 := by decide
  rcases family_descends (prefixWord ++ tailWord_87169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87178 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 5, 4]
def baseStart_87178 : Nat := 118140960795 + 87178 * 2 ^ 59
def prefixEnd_87178 : Nat := 4983230072969 + 3 ^ 40 * 87178 * 2
def baseEnd_87178 : Nat := 29842810998510099582721

theorem tailTrace_87178 : CollatzResearch.WordTrace tailWord_87178 prefixEnd_87178 29842810998510099582721 := by
  unfold tailWord_87178
  simp only [CollatzResearch.WordTrace]
  refine ⟨794910719544117415537547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2119761918784313108100125 794910719544117415537547)
  ·
    refine ⟨1192366079316176123306321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 794910719544117415537547 1192366079316176123306321)
    ·
      refine ⟨894274559487132092479741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1192366079316176123306321 894274559487132092479741)
      ·
        refine ⟨335352959807674534679903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 894274559487132092479741 335352959807674534679903)
        ·
          refine ⟨503029439711511802019855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335352959807674534679903 503029439711511802019855)
          ·
            refine ⟨754544159567267703029783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 503029439711511802019855 754544159567267703029783)
            ·
              refine ⟨1131816239350901554544675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 754544159567267703029783 1131816239350901554544675)
              ·
                refine ⟨1697724359026352331817013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1131816239350901554544675 1697724359026352331817013)
                ·
                  refine ⟨159161658658720531107845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1697724359026352331817013 159161658658720531107845)
                  ·
                    refine ⟨29842810998510099582721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 159161658658720531107845 29842810998510099582721)
                    ·
                      rfl

theorem cell22_87178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_87178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87178 prefixEnd_87178 := by exact prefixLift 87178
  have htrace : WordTrace (prefixWord ++ tailWord_87178) baseStart_87178 baseEnd_87178 := by
    simpa [prefixWord, tailWord_87178, baseEnd_87178] using wordTrace_append hprefix tailTrace_87178
  have hstable : (prefixWord ++ tailWord_87178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87178).length < 2 ^ (prefixWord ++ tailWord_87178).sum := by decide
  have hdescent : baseEnd_87178 < baseStart_87178 := by decide
  rcases family_descends (prefixWord ++ tailWord_87178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87223 : List Nat := [1, 1, 3, 1, 4, 1, 2, 1, 4, 4]
def baseStart_87223 : Nat := 118140960795 + 87223 * 2 ^ 59
def prefixEnd_87223 : Nat := 4983230072969 + 3 ^ 40 * 87223 * 2
def baseEnd_87223 : Nat := 29858215418144982207583

theorem tailTrace_87223 : CollatzResearch.WordTrace tailWord_87223 prefixEnd_87223 29858215418144982207583 := by
  unfold tailWord_87223
  simp only [CollatzResearch.WordTrace]
  refine ⟨3181284163013442347538323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2120856108675628231692215 3181284163013442347538323)
  ·
    refine ⟨4771926244520163521307485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3181284163013442347538323 4771926244520163521307485)
    ·
      refine ⟨1789472341695061320490307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4771926244520163521307485 1789472341695061320490307)
      ·
        refine ⟨2684208512542591980735461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1789472341695061320490307 2684208512542591980735461)
        ·
          refine ⟨503289096101735996387899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2684208512542591980735461 503289096101735996387899)
          ·
            refine ⟨754933644152603994581849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 503289096101735996387899 754933644152603994581849)
            ·
              refine ⟨566200233114452995936387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 754933644152603994581849 566200233114452995936387)
              ·
                refine ⟨849300349671679493904581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 566200233114452995936387 849300349671679493904581)
                ·
                  refine ⟨159243815563439905107109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 849300349671679493904581 159243815563439905107109)
                  ·
                    refine ⟨29858215418144982207583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 159243815563439905107109 29858215418144982207583)
                    ·
                      rfl

theorem cell22_87223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 4].length) (baseStart_87223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87223 prefixEnd_87223 := by exact prefixLift 87223
  have htrace : WordTrace (prefixWord ++ tailWord_87223) baseStart_87223 baseEnd_87223 := by
    simpa [prefixWord, tailWord_87223, baseEnd_87223] using wordTrace_append hprefix tailTrace_87223
  have hstable : (prefixWord ++ tailWord_87223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87223).length < 2 ^ (prefixWord ++ tailWord_87223).sum := by decide
  have hdescent : baseEnd_87223 < baseStart_87223 := by decide
  rcases family_descends (prefixWord ++ tailWord_87223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87225 : List Nat := [1, 2, 1, 4, 1, 4, 1, 1, 4, 3]
def baseStart_87225 : Nat := 118140960795 + 87225 * 2 ^ 59
def prefixEnd_87225 : Nat := 4983230072969 + 3 ^ 40 * 87225 * 2
def baseEnd_87225 : Nat := 29858900059017643657577

theorem tailTrace_87225 : CollatzResearch.WordTrace tailWord_87225 prefixEnd_87225 29858900059017643657577 := by
  unfold tailWord_87225
  simp only [CollatzResearch.WordTrace]
  refine ⟨3181357109006196689111129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2120904739337464459407419 3181357109006196689111129)
  ·
    refine ⟨2386017831754647516833347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3181357109006196689111129 2386017831754647516833347)
    ·
      refine ⟨3579026747631971275250021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2386017831754647516833347 3579026747631971275250021)
      ·
        refine ⟨671067515180994614109379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3579026747631971275250021 671067515180994614109379)
        ·
          refine ⟨1006601272771491921164069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 671067515180994614109379 1006601272771491921164069)
          ·
            refine ⟨188737738644654735218263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1006601272771491921164069 188737738644654735218263)
            ·
              refine ⟨283106607966982102827395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188737738644654735218263 283106607966982102827395)
              ·
                refine ⟨424659911950473154241093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 283106607966982102827395 424659911950473154241093)
                ·
                  refine ⟨79623733490713716420205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 424659911950473154241093 79623733490713716420205)
                  ·
                    refine ⟨29858900059017643657577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79623733490713716420205 29858900059017643657577)
                    ·
                      rfl

theorem cell22_87225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 4, 3].length) (baseStart_87225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87225 prefixEnd_87225 := by exact prefixLift 87225
  have htrace : WordTrace (prefixWord ++ tailWord_87225) baseStart_87225 baseEnd_87225 := by
    simpa [prefixWord, tailWord_87225, baseEnd_87225] using wordTrace_append hprefix tailTrace_87225
  have hstable : (prefixWord ++ tailWord_87225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87225).length < 2 ^ (prefixWord ++ tailWord_87225).sum := by decide
  have hdescent : baseEnd_87225 < baseStart_87225 := by decide
  rcases family_descends (prefixWord ++ tailWord_87225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87261 : List Nat := [1, 4, 3, 2, 3, 1, 1, 3, 4]
def baseStart_87261 : Nat := 118140960795 + 87261 * 2 ^ 59
def prefixEnd_87261 : Nat := 4983230072969 + 3 ^ 40 * 87261 * 2
def baseEnd_87261 : Nat := 9957074531575183252489

theorem tailTrace_87261 : CollatzResearch.WordTrace tailWord_87261 prefixEnd_87261 9957074531575183252489 := by
  unfold tailWord_87261
  simp only [CollatzResearch.WordTrace]
  refine ⟨3182670136875774837421637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2121780091250516558281091 3182670136875774837421637)
  ·
    refine ⟨596750650664207782016557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3182670136875774837421637 596750650664207782016557)
    ·
      refine ⟨223781493999077918256209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 596750650664207782016557 223781493999077918256209)
      ·
        refine ⟨167836120499308438692157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223781493999077918256209 167836120499308438692157)
        ·
          refine ⟨62938545187240664509559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167836120499308438692157 62938545187240664509559)
          ·
            refine ⟨94407817780860996764339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62938545187240664509559 94407817780860996764339)
            ·
              refine ⟨141611726671291495146509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94407817780860996764339 141611726671291495146509)
              ·
                refine ⟨53104397501734310679941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141611726671291495146509 53104397501734310679941)
                ·
                  refine ⟨9957074531575183252489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53104397501734310679941 9957074531575183252489)
                  ·
                    rfl

theorem cell22_87261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 3, 4].length) (baseStart_87261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87261 prefixEnd_87261 := by exact prefixLift 87261
  have htrace : WordTrace (prefixWord ++ tailWord_87261) baseStart_87261 baseEnd_87261 := by
    simpa [prefixWord, tailWord_87261, baseEnd_87261] using wordTrace_append hprefix tailTrace_87261
  have hstable : (prefixWord ++ tailWord_87261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87261).length < 2 ^ (prefixWord ++ tailWord_87261).sum := by decide
  have hdescent : baseEnd_87261 < baseStart_87261 := by decide
  rcases family_descends (prefixWord ++ tailWord_87261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87283 : List Nat := [1, 1, 1, 2, 2, 5, 2, 1, 7]
def baseStart_87283 : Nat := 118140960795 + 87283 * 2 ^ 59
def prefixEnd_87283 : Nat := 4983230072969 + 3 ^ 40 * 87283 * 2
def baseEnd_87283 : Nat := 9959584881441608569133

theorem tailTrace_87283 : CollatzResearch.WordTrace tailWord_87283 prefixEnd_87283 9959584881441608569133 := by
  unfold tailWord_87283
  simp only [CollatzResearch.WordTrace]
  refine ⟨3183472542796072594722503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2122315028530715063148335 3183472542796072594722503)
  ·
    refine ⟨4775208814194108892083755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3183472542796072594722503 4775208814194108892083755)
    ·
      refine ⟨7162813221291163338125633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4775208814194108892083755 7162813221291163338125633)
      ·
        refine ⟨5372109915968372503594225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7162813221291163338125633 5372109915968372503594225)
        ·
          refine ⟨4029082436976279377695669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5372109915968372503594225 4029082436976279377695669)
          ·
            refine ⟨377726478466526191658969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4029082436976279377695669 377726478466526191658969)
            ·
              refine ⟨283294858849894643744227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 377726478466526191658969 283294858849894643744227)
              ·
                refine ⟨424942288274841965616341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 283294858849894643744227 424942288274841965616341)
                ·
                  refine ⟨9959584881441608569133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 424942288274841965616341 9959584881441608569133)
                  ·
                    rfl

theorem cell22_87283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 7].length) (baseStart_87283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87283 prefixEnd_87283 := by exact prefixLift 87283
  have htrace : WordTrace (prefixWord ++ tailWord_87283) baseStart_87283 baseEnd_87283 := by
    simpa [prefixWord, tailWord_87283, baseEnd_87283] using wordTrace_append hprefix tailTrace_87283
  have hstable : (prefixWord ++ tailWord_87283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87283).length < 2 ^ (prefixWord ++ tailWord_87283).sum := by decide
  have hdescent : baseEnd_87283 < baseStart_87283 := by decide
  rcases family_descends (prefixWord ++ tailWord_87283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87338 : List Nat := [3, 1, 4, 2, 1, 3, 2, 2, 1, 3]
def baseStart_87338 : Nat := 118140960795 + 87338 * 2 ^ 59
def prefixEnd_87338 : Nat := 4983230072969 + 3 ^ 40 * 87338 * 2
def baseEnd_87338 : Nat := 29897582268323015582231

theorem tailTrace_87338 : CollatzResearch.WordTrace tailWord_87338 prefixEnd_87338 29897582268323015582231 := by
  unfold tailWord_87338
  simp only [CollatzResearch.WordTrace]
  refine ⟨796369639399204246993667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2123652371731211325316445 796369639399204246993667)
  ·
    refine ⟨1194554459098806370490501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 796369639399204246993667 1194554459098806370490501)
    ·
      refine ⟨223978961081026194466969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1194554459098806370490501 223978961081026194466969)
      ·
        refine ⟨167984220810769645850227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223978961081026194466969 167984220810769645850227)
        ·
          refine ⟨251976331216154468775341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167984220810769645850227 251976331216154468775341)
          ·
            refine ⟨94491124206057925790753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 251976331216154468775341 94491124206057925790753)
            ·
              refine ⟨70868343154543444343065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94491124206057925790753 70868343154543444343065)
              ·
                refine ⟨53151257365907583257299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70868343154543444343065 53151257365907583257299)
                ·
                  refine ⟨79726886048861374885949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53151257365907583257299 79726886048861374885949)
                  ·
                    refine ⟨29897582268323015582231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79726886048861374885949 29897582268323015582231)
                    ·
                      rfl

theorem cell22_87338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_87338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87338 prefixEnd_87338 := by exact prefixLift 87338
  have htrace : WordTrace (prefixWord ++ tailWord_87338) baseStart_87338 baseEnd_87338 := by
    simpa [prefixWord, tailWord_87338, baseEnd_87338] using wordTrace_append hprefix tailTrace_87338
  have hstable : (prefixWord ++ tailWord_87338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87338).length < 2 ^ (prefixWord ++ tailWord_87338).sum := by decide
  have hdescent : baseEnd_87338 < baseStart_87338 := by decide
  rcases family_descends (prefixWord ++ tailWord_87338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87343 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 5, 5]
def baseStart_87343 : Nat := 118140960795 + 87343 * 2 ^ 59
def prefixEnd_87343 : Nat := 4983230072969 + 3 ^ 40 * 87343 * 2
def baseEnd_87343 : Nat := 29899293870504669207215

theorem tailTrace_87343 : CollatzResearch.WordTrace tailWord_87343 prefixEnd_87343 29899293870504669207215 := by
  unfold tailWord_87343
  simp only [CollatzResearch.WordTrace]
  refine ⟨3185660922578702841906683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2123773948385801894604455 3185660922578702841906683)
  ·
    refine ⟨4778491383868054262860025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3185660922578702841906683 4778491383868054262860025)
    ·
      refine ⟨3583868537901040697145019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4778491383868054262860025 3583868537901040697145019)
      ·
        refine ⟨5375802806851561045717529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3583868537901040697145019 5375802806851561045717529)
        ·
          refine ⟨4031852105138670784288147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5375802806851561045717529 4031852105138670784288147)
          ·
            refine ⟨6047778157708006176432221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4031852105138670784288147 6047778157708006176432221)
            ·
              refine ⟨2267916809140502316162083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6047778157708006176432221 2267916809140502316162083)
              ·
                refine ⟨3401875213710753474243125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2267916809140502316162083 3401875213710753474243125)
                ·
                  refine ⟨318925801285383138210293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3401875213710753474243125 318925801285383138210293)
                  ·
                    refine ⟨29899293870504669207215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 318925801285383138210293 29899293870504669207215)
                    ·
                      rfl

theorem cell22_87343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 5].length) (baseStart_87343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87343 prefixEnd_87343 := by exact prefixLift 87343
  have htrace : WordTrace (prefixWord ++ tailWord_87343) baseStart_87343 baseEnd_87343 := by
    simpa [prefixWord, tailWord_87343, baseEnd_87343] using wordTrace_append hprefix tailTrace_87343
  have hstable : (prefixWord ++ tailWord_87343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87343).length < 2 ^ (prefixWord ++ tailWord_87343).sum := by decide
  have hdescent : baseEnd_87343 < baseStart_87343 := by decide
  rcases family_descends (prefixWord ++ tailWord_87343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87360 : List Nat := [2, 1, 1, 2, 2, 1, 6, 1, 1, 5]
def baseStart_87360 : Nat := 118140960795 + 87360 * 2 ^ 59
def prefixEnd_87360 : Nat := 4983230072969 + 3 ^ 40 * 87360 * 2
def baseEnd_87360 : Nat := 29905113317922291532163

theorem tailTrace_87360 : CollatzResearch.WordTrace tailWord_87360 prefixEnd_87360 29905113317922291532163 := by
  unfold tailWord_87360
  simp only [CollatzResearch.WordTrace]
  refine ⟨1593140481758557372637767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2124187309011409830183689 1593140481758557372637767)
  ·
    refine ⟨2389710722637836058956651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1593140481758557372637767 2389710722637836058956651)
    ·
      refine ⟨3584566083956754088434977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2389710722637836058956651 3584566083956754088434977)
      ·
        refine ⟨2688424562967565566326233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3584566083956754088434977 2688424562967565566326233)
        ·
          refine ⟨2016318422225674174744675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2688424562967565566326233 2016318422225674174744675)
          ·
            refine ⟨3024477633338511262117013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2016318422225674174744675 3024477633338511262117013)
            ·
              refine ⟨141772389062742715411735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3024477633338511262117013 141772389062742715411735)
              ·
                refine ⟨212658583594114073117603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141772389062742715411735 212658583594114073117603)
                ·
                  refine ⟨318987875391171109676405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 212658583594114073117603 318987875391171109676405)
                  ·
                    refine ⟨29905113317922291532163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 318987875391171109676405 29905113317922291532163)
                    ·
                      rfl

theorem cell22_87360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 1, 1, 5].length) (baseStart_87360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87360 prefixEnd_87360 := by exact prefixLift 87360
  have htrace : WordTrace (prefixWord ++ tailWord_87360) baseStart_87360 baseEnd_87360 := by
    simpa [prefixWord, tailWord_87360, baseEnd_87360] using wordTrace_append hprefix tailTrace_87360
  have hstable : (prefixWord ++ tailWord_87360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87360).length < 2 ^ (prefixWord ++ tailWord_87360).sum := by decide
  have hdescent : baseEnd_87360 < baseStart_87360 := by decide
  rcases family_descends (prefixWord ++ tailWord_87360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87456 : List Nat := [2, 1, 1, 4, 1, 2, 5, 2, 1, 3]
def baseStart_87456 : Nat := 118140960795 + 87456 * 2 ^ 59
def prefixEnd_87456 : Nat := 4983230072969 + 3 ^ 40 * 87456 * 2
def baseEnd_87456 : Nat := 29937976079810041131869

theorem tailTrace_87456 : CollatzResearch.WordTrace tailWord_87456 prefixEnd_87456 29937976079810041131869 := by
  unfold tailWord_87456
  simp only [CollatzResearch.WordTrace]
  refine ⟨1594891185584661570385111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2126521580779548760513481 1594891185584661570385111)
  ·
    refine ⟨2392336778376992355577667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1594891185584661570385111 2392336778376992355577667)
    ·
      refine ⟨3588505167565488533366501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2392336778376992355577667 3588505167565488533366501)
      ·
        refine ⟨672844718918529100006219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3588505167565488533366501 672844718918529100006219)
        ·
          refine ⟨1009267078377793650009329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 672844718918529100006219 1009267078377793650009329)
          ·
            refine ⟨756950308783345237506997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1009267078377793650009329 756950308783345237506997)
            ·
              refine ⟨70964091448438616016281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 756950308783345237506997 70964091448438616016281)
              ·
                refine ⟨53223068586328962012211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70964091448438616016281 53223068586328962012211)
                ·
                  refine ⟨79834602879493443018317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53223068586328962012211 79834602879493443018317)
                  ·
                    refine ⟨29937976079810041131869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79834602879493443018317 29937976079810041131869)
                    ·
                      rfl

theorem cell22_87456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 2, 1, 3].length) (baseStart_87456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87456 prefixEnd_87456 := by exact prefixLift 87456
  have htrace : WordTrace (prefixWord ++ tailWord_87456) baseStart_87456 baseEnd_87456 := by
    simpa [prefixWord, tailWord_87456, baseEnd_87456] using wordTrace_append hprefix tailTrace_87456
  have hstable : (prefixWord ++ tailWord_87456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87456).length < 2 ^ (prefixWord ++ tailWord_87456).sum := by decide
  have hdescent : baseEnd_87456 < baseStart_87456 := by decide
  rcases family_descends (prefixWord ++ tailWord_87456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87469 : List Nat := [1, 5, 2, 2, 1, 2, 1, 3, 5]
def baseStart_87469 : Nat := 118140960795 + 87469 * 2 ^ 59
def prefixEnd_87469 : Nat := 4983230072969 + 3 ^ 40 * 87469 * 2
def baseEnd_87469 : Nat := 9980808748494113518943

theorem tailTrace_87469 : CollatzResearch.WordTrace tailWord_87469 prefixEnd_87469 9980808748494113518943 := by
  unfold tailWord_87469
  simp only [CollatzResearch.WordTrace]
  refine ⟨3190256520122226360993461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2126837680081484240662307 3190256520122226360993461)
  ·
    refine ⟨299086548761458721343137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3190256520122226360993461 299086548761458721343137)
    ·
      refine ⟨224314911571094041007353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299086548761458721343137 224314911571094041007353)
      ·
        refine ⟨168236183678320530755515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224314911571094041007353 168236183678320530755515)
        ·
          refine ⟨252354275517480796133273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168236183678320530755515 252354275517480796133273)
          ·
            refine ⟨189265706638110597099955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252354275517480796133273 189265706638110597099955)
            ·
              refine ⟨283898559957165895649933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189265706638110597099955 283898559957165895649933)
              ·
                refine ⟨106461959983937210868725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 283898559957165895649933 106461959983937210868725)
                ·
                  refine ⟨9980808748494113518943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106461959983937210868725 9980808748494113518943)
                  ·
                    rfl

theorem cell22_87469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_87469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87469 prefixEnd_87469 := by exact prefixLift 87469
  have htrace : WordTrace (prefixWord ++ tailWord_87469) baseStart_87469 baseEnd_87469 := by
    simpa [prefixWord, tailWord_87469, baseEnd_87469] using wordTrace_append hprefix tailTrace_87469
  have hstable : (prefixWord ++ tailWord_87469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87469).length < 2 ^ (prefixWord ++ tailWord_87469).sum := by decide
  have hdescent : baseEnd_87469 < baseStart_87469 := by decide
  rcases family_descends (prefixWord ++ tailWord_87469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87480 : List Nat := [2, 1, 2, 1, 2, 2, 2, 4, 6]
def baseStart_87480 : Nat := 118140960795 + 87480 * 2 ^ 59
def prefixEnd_87480 : Nat := 4983230072969 + 3 ^ 40 * 87480 * 2
def baseEnd_87480 : Nat := 9982063923427326177265

theorem tailTrace_87480 : CollatzResearch.WordTrace tailWord_87480 prefixEnd_87480 9982063923427326177265 := by
  unfold tailWord_87480
  simp only [CollatzResearch.WordTrace]
  refine ⟨1595328861541187619821947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2127105148721583493095929 1595328861541187619821947)
  ·
    refine ⟨2392993292311781429732921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1595328861541187619821947 2392993292311781429732921)
    ·
      refine ⟨1794744969233836072299691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2392993292311781429732921 1794744969233836072299691)
      ·
        refine ⟨2692117453850754108449537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1794744969233836072299691 2692117453850754108449537)
        ·
          refine ⟨2019088090388065581337153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2692117453850754108449537 2019088090388065581337153)
          ·
            refine ⟨1514316067791049186002865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2019088090388065581337153 1514316067791049186002865)
            ·
              refine ⟨1135737050843286889502149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1514316067791049186002865 1135737050843286889502149)
              ·
                refine ⟨212950697033116291781653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1135737050843286889502149 212950697033116291781653)
                ·
                  refine ⟨9982063923427326177265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 212950697033116291781653 9982063923427326177265)
                  ·
                    rfl

theorem cell22_87480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 6].length) (baseStart_87480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87480 prefixEnd_87480 := by exact prefixLift 87480
  have htrace : WordTrace (prefixWord ++ tailWord_87480) baseStart_87480 baseEnd_87480 := by
    simpa [prefixWord, tailWord_87480, baseEnd_87480] using wordTrace_append hprefix tailTrace_87480
  have hstable : (prefixWord ++ tailWord_87480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87480).length < 2 ^ (prefixWord ++ tailWord_87480).sum := by decide
  have hdescent : baseEnd_87480 < baseStart_87480 := by decide
  rcases family_descends (prefixWord ++ tailWord_87480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87497 : List Nat := [1, 2, 1, 1, 2, 1, 3, 7, 4]
def baseStart_87497 : Nat := 118140960795 + 87497 * 2 ^ 59
def prefixEnd_87497 : Nat := 4983230072969 + 3 ^ 40 * 87497 * 2
def baseEnd_87497 : Nat := 9984003739233200285581

theorem tailTrace_87497 : CollatzResearch.WordTrace tailWord_87497 prefixEnd_87497 9984003739233200285581 := by
  unfold tailWord_87497
  simp only [CollatzResearch.WordTrace]
  refine ⟨3191277764020787143012745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2127518509347191428675163 3191277764020787143012745)
  ·
    refine ⟨2393458323015590357259559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3191277764020787143012745 2393458323015590357259559)
    ·
      refine ⟨3590187484523385535889339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2393458323015590357259559 3590187484523385535889339)
      ·
        refine ⟨5385281226785078303834009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3590187484523385535889339 5385281226785078303834009)
        ·
          refine ⟨4038960920088808727875507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5385281226785078303834009 4038960920088808727875507)
          ·
            refine ⟨6058441380133213091813261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4038960920088808727875507 6058441380133213091813261)
            ·
              refine ⟨2271915517549954909429973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6058441380133213091813261 2271915517549954909429973)
              ·
                refine ⟨53248019942577068189765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2271915517549954909429973 53248019942577068189765)
                ·
                  refine ⟨9984003739233200285581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53248019942577068189765 9984003739233200285581)
                  ·
                    rfl

theorem cell22_87497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 7, 4].length) (baseStart_87497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87497 prefixEnd_87497 := by exact prefixLift 87497
  have htrace : WordTrace (prefixWord ++ tailWord_87497) baseStart_87497 baseEnd_87497 := by
    simpa [prefixWord, tailWord_87497, baseEnd_87497] using wordTrace_append hprefix tailTrace_87497
  have hstable : (prefixWord ++ tailWord_87497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87497).length < 2 ^ (prefixWord ++ tailWord_87497).sum := by decide
  have hdescent : baseEnd_87497 < baseStart_87497 := by decide
  rcases family_descends (prefixWord ++ tailWord_87497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87512 : List Nat := [2, 1, 2, 2, 2, 1, 2, 3, 4, 3]
def baseStart_87512 : Nat := 118140960795 + 87512 * 2 ^ 59
def prefixEnd_87512 : Nat := 4983230072969 + 3 ^ 40 * 87512 * 2
def baseEnd_87512 : Nat := 29957146024244561731697

theorem tailTrace_87512 : CollatzResearch.WordTrace tailWord_87512 prefixEnd_87512 29957146024244561731697 := by
  unfold tailWord_87512
  simp only [CollatzResearch.WordTrace]
  refine ⟨1595912429483222352404395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2127883239310963136539193 1595912429483222352404395)
  ·
    refine ⟨2393868644224833528606593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1595912429483222352404395 2393868644224833528606593)
    ·
      refine ⟨1795401483168625146454945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2393868644224833528606593 1795401483168625146454945)
      ·
        refine ⟨1346551112376468859841209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1795401483168625146454945 1346551112376468859841209)
        ·
          refine ⟨1009913334282351644880907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1346551112376468859841209 1009913334282351644880907)
          ·
            refine ⟨1514870001423527467321361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1009913334282351644880907 1514870001423527467321361)
            ·
              refine ⟨1136152501067645600491021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1514870001423527467321361 1136152501067645600491021)
              ·
                refine ⟨426057187900367100184133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1136152501067645600491021 426057187900367100184133)
                ·
                  refine ⟨79885722731318831284525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 426057187900367100184133 79885722731318831284525)
                  ·
                    refine ⟨29957146024244561731697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79885722731318831284525 29957146024244561731697)
                    ·
                      rfl

theorem cell22_87512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 4, 3].length) (baseStart_87512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87512 prefixEnd_87512 := by exact prefixLift 87512
  have htrace : WordTrace (prefixWord ++ tailWord_87512) baseStart_87512 baseEnd_87512 := by
    simpa [prefixWord, tailWord_87512, baseEnd_87512] using wordTrace_append hprefix tailTrace_87512
  have hstable : (prefixWord ++ tailWord_87512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87512).length < 2 ^ (prefixWord ++ tailWord_87512).sum := by decide
  have hdescent : baseEnd_87512 < baseStart_87512 := by decide
  rcases family_descends (prefixWord ++ tailWord_87512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87514 : List Nat := [3, 1, 1, 2, 3, 3, 1, 4, 4]
def baseStart_87514 : Nat := 118140960795 + 87514 * 2 ^ 59
def prefixEnd_87514 : Nat := 4983230072969 + 3 ^ 40 * 87514 * 2
def baseEnd_87514 : Nat := 9985943555039074393897

theorem tailTrace_87514 : CollatzResearch.WordTrace tailWord_87514 prefixEnd_87514 9985943555039074393897 := by
  unfold tailWord_87514
  simp only [CollatzResearch.WordTrace]
  refine ⟨797974451239799761595399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2127931869972799364254397 797974451239799761595399)
  ·
    refine ⟨1196961676859699642393099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 797974451239799761595399 1196961676859699642393099)
    ·
      refine ⟨1795442515289549463589649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1196961676859699642393099 1795442515289549463589649)
      ·
        refine ⟨1346581886467162097692237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1795442515289549463589649 1346581886467162097692237)
        ·
          refine ⟨504968207425185786634589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1346581886467162097692237 504968207425185786634589)
          ·
            refine ⟨189363077784444669987971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 504968207425185786634589 189363077784444669987971)
            ·
              refine ⟨284044616676667004981957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189363077784444669987971 284044616676667004981957)
              ·
                refine ⟨53258365626875063434117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 284044616676667004981957 53258365626875063434117)
                ·
                  refine ⟨9985943555039074393897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53258365626875063434117 9985943555039074393897)
                  ·
                    rfl

theorem cell22_87514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 4, 4].length) (baseStart_87514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87514 prefixEnd_87514 := by exact prefixLift 87514
  have htrace : WordTrace (prefixWord ++ tailWord_87514) baseStart_87514 baseEnd_87514 := by
    simpa [prefixWord, tailWord_87514, baseEnd_87514] using wordTrace_append hprefix tailTrace_87514
  have hstable : (prefixWord ++ tailWord_87514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87514).length < 2 ^ (prefixWord ++ tailWord_87514).sum := by decide
  have hdescent : baseEnd_87514 < baseStart_87514 := by decide
  rcases family_descends (prefixWord ++ tailWord_87514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87544 : List Nat := [2, 1, 2, 1, 1, 7, 1, 1, 2, 4]
def baseStart_87544 : Nat := 118140960795 + 87544 * 2 ^ 59
def prefixEnd_87544 : Nat := 4983230072969 + 3 ^ 40 * 87544 * 2
def baseEnd_87544 : Nat := 29968100278207144931599

theorem tailTrace_87544 : CollatzResearch.WordTrace tailWord_87544 prefixEnd_87544 29968100278207144931599 := by
  unfold tailWord_87544
  simp only [CollatzResearch.WordTrace]
  refine ⟨1596495997425257084986843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2128661329900342779982457 1596495997425257084986843)
  ·
    refine ⟨2394743996137885627480265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1596495997425257084986843 2394743996137885627480265)
    ·
      refine ⟨1796057997103414220610199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2394743996137885627480265 1796057997103414220610199)
      ·
        refine ⟨2694086995655121330915299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1796057997103414220610199 2694086995655121330915299)
        ·
          refine ⟨4041130493482681996372949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2694086995655121330915299 4041130493482681996372949)
          ·
            refine ⟨94713995941000359289991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 4041130493482681996372949 94713995941000359289991)
            ·
              refine ⟨142070993911500538934987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94713995941000359289991 142070993911500538934987)
              ·
                refine ⟨213106490867250808402481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142070993911500538934987 213106490867250808402481)
                ·
                  refine ⟨159829868150438106301861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213106490867250808402481 159829868150438106301861)
                  ·
                    refine ⟨29968100278207144931599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 159829868150438106301861 29968100278207144931599)
                    ·
                      rfl

theorem cell22_87544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 2, 4].length) (baseStart_87544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87544 prefixEnd_87544 := by exact prefixLift 87544
  have htrace : WordTrace (prefixWord ++ tailWord_87544) baseStart_87544 baseEnd_87544 := by
    simpa [prefixWord, tailWord_87544, baseEnd_87544] using wordTrace_append hprefix tailTrace_87544
  have hstable : (prefixWord ++ tailWord_87544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87544).length < 2 ^ (prefixWord ++ tailWord_87544).sum := by decide
  have hdescent : baseEnd_87544 < baseStart_87544 := by decide
  rcases family_descends (prefixWord ++ tailWord_87544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87550 : List Nat := [4, 2, 2, 3, 1, 2, 2, 1, 1, 4]
def baseStart_87550 : Nat := 118140960795 + 87550 * 2 ^ 59
def prefixEnd_87550 : Nat := 4983230072969 + 3 ^ 40 * 87550 * 2
def baseEnd_87550 : Nat := 29970154200825129281581

theorem tailTrace_87550 : CollatzResearch.WordTrace tailWord_87550 prefixEnd_87550 29970154200825129281581 := by
  unfold tailWord_87550
  simp only [CollatzResearch.WordTrace]
  refine ⟨399151354103597149336513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2128807221885851463128069 399151354103597149336513)
  ·
    refine ⟨299363515577697862002385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 399151354103597149336513 299363515577697862002385)
    ·
      refine ⟨224522636683273396501789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299363515577697862002385 224522636683273396501789)
      ·
        refine ⟨84195988756227523688171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224522636683273396501789 84195988756227523688171)
        ·
          refine ⟨126293983134341285532257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84195988756227523688171 126293983134341285532257)
          ·
            refine ⟨94720487350755964149193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126293983134341285532257 94720487350755964149193)
            ·
              refine ⟨71040365513066973111895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94720487350755964149193 71040365513066973111895)
              ·
                refine ⟨106560548269600459667843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71040365513066973111895 106560548269600459667843)
                ·
                  refine ⟨159840822404400689501765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106560548269600459667843 159840822404400689501765)
                  ·
                    refine ⟨29970154200825129281581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 159840822404400689501765 29970154200825129281581)
                    ·
                      rfl

theorem cell22_87550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 1, 4].length) (baseStart_87550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87550 prefixEnd_87550 := by exact prefixLift 87550
  have htrace : WordTrace (prefixWord ++ tailWord_87550) baseStart_87550 baseEnd_87550 := by
    simpa [prefixWord, tailWord_87550, baseEnd_87550] using wordTrace_append hprefix tailTrace_87550
  have hstable : (prefixWord ++ tailWord_87550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87550).length < 2 ^ (prefixWord ++ tailWord_87550).sum := by decide
  have hdescent : baseEnd_87550 < baseStart_87550 := by decide
  rcases family_descends (prefixWord ++ tailWord_87550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87555 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 1, 8]
def baseStart_87555 : Nat := 118140960795 + 87555 * 2 ^ 59
def prefixEnd_87555 : Nat := 4983230072969 + 3 ^ 40 * 87555 * 2
def baseEnd_87555 : Nat := 29971865803006782906565

theorem tailTrace_87555 : CollatzResearch.WordTrace tailWord_87555 prefixEnd_87555 29971865803006782906565 := by
  unfold tailWord_87555
  simp only [CollatzResearch.WordTrace]
  refine ⟨3193393197810663048624119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2128928798540442032416079 3193393197810663048624119)
  ·
    refine ⟨4790089796715994572936179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3193393197810663048624119 4790089796715994572936179)
    ·
      refine ⟨7185134695073991859404269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4790089796715994572936179 7185134695073991859404269)
      ·
        refine ⟨2694425510652746947276601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7185134695073991859404269 2694425510652746947276601)
        ·
          refine ⟨2020819132989560210457451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2694425510652746947276601 2020819132989560210457451)
          ·
            refine ⟨3031228699484340315686177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2020819132989560210457451 3031228699484340315686177)
            ·
              refine ⟨2273421524613255236764633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3031228699484340315686177 2273421524613255236764633)
              ·
                refine ⟨1705066143459941427573475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2273421524613255236764633 1705066143459941427573475)
                ·
                  refine ⟨2557599215189912141360213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1705066143459941427573475 2557599215189912141360213)
                  ·
                    refine ⟨29971865803006782906565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2557599215189912141360213 29971865803006782906565)
                    ·
                      rfl

theorem cell22_87555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 8].length) (baseStart_87555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87555 prefixEnd_87555 := by exact prefixLift 87555
  have htrace : WordTrace (prefixWord ++ tailWord_87555) baseStart_87555 baseEnd_87555 := by
    simpa [prefixWord, tailWord_87555, baseEnd_87555] using wordTrace_append hprefix tailTrace_87555
  have hstable : (prefixWord ++ tailWord_87555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87555).length < 2 ^ (prefixWord ++ tailWord_87555).sum := by decide
  have hdescent : baseEnd_87555 < baseStart_87555 := by decide
  rcases family_descends (prefixWord ++ tailWord_87555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87557 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 7, 3]
def baseStart_87557 : Nat := 118140960795 + 87557 * 2 ^ 59
def prefixEnd_87557 : Nat := 4983230072969 + 3 ^ 40 * 87557 * 2
def baseEnd_87557 : Nat := 29972550443879444356559

theorem tailTrace_87557 : CollatzResearch.WordTrace tailWord_87557 prefixEnd_87557 29972550443879444356559 := by
  unfold tailWord_87557
  simp only [CollatzResearch.WordTrace]
  refine ⟨3193466143803417390196925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2128977429202278260131283 3193466143803417390196925)
  ·
    refine ⟨1197549803926281521323847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3193466143803417390196925 1197549803926281521323847)
    ·
      refine ⟨1796324705889422281985771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1197549803926281521323847 1796324705889422281985771)
      ·
        refine ⟨2694487058834133422978657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1796324705889422281985771 2694487058834133422978657)
        ·
          refine ⟨2020865294125600067233993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2694487058834133422978657 2020865294125600067233993)
          ·
            refine ⟨1515648970594200050425495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2020865294125600067233993 1515648970594200050425495)
            ·
              refine ⟨2273473455891300075638243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1515648970594200050425495 2273473455891300075638243)
              ·
                refine ⟨3410210183836950113457365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2273473455891300075638243 3410210183836950113457365)
                ·
                  refine ⟨79926801183678518284157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3410210183836950113457365 79926801183678518284157)
                  ·
                    refine ⟨29972550443879444356559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79926801183678518284157 29972550443879444356559)
                    ·
                      rfl

theorem cell22_87557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 7, 3].length) (baseStart_87557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87557 prefixEnd_87557 := by exact prefixLift 87557
  have htrace : WordTrace (prefixWord ++ tailWord_87557) baseStart_87557 baseEnd_87557 := by
    simpa [prefixWord, tailWord_87557, baseEnd_87557] using wordTrace_append hprefix tailTrace_87557
  have hstable : (prefixWord ++ tailWord_87557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87557).length < 2 ^ (prefixWord ++ tailWord_87557).sum := by decide
  have hdescent : baseEnd_87557 < baseStart_87557 := by decide
  rcases family_descends (prefixWord ++ tailWord_87557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87563 : List Nat := [1, 1, 1, 1, 9, 1, 1, 2, 2, 3]
def baseStart_87563 : Nat := 118140960795 + 87563 * 2 ^ 59
def prefixEnd_87563 : Nat := 4983230072969 + 3 ^ 40 * 87563 * 2
def baseEnd_87563 : Nat := 29974604366497428706541

theorem tailTrace_87563 : CollatzResearch.WordTrace tailWord_87563 prefixEnd_87563 29974604366497428706541 := by
  unfold tailWord_87563
  simp only [CollatzResearch.WordTrace]
  refine ⟨3193684981781680414915343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2129123321187786943276895 3193684981781680414915343)
  ·
    refine ⟨4790527472672520622373015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3193684981781680414915343 4790527472672520622373015)
    ·
      refine ⟨7185791209008780933559523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4790527472672520622373015 7185791209008780933559523)
      ·
        refine ⟨10778686813513171400339285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7185791209008780933559523 10778686813513171400339285)
        ·
          refine ⟨63156368047928738673863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 10778686813513171400339285 63156368047928738673863)
          ·
            refine ⟨94734552071893108010795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63156368047928738673863 94734552071893108010795)
            ·
              refine ⟨142101828107839662016193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94734552071893108010795 142101828107839662016193)
              ·
                refine ⟨106576371080879746512145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142101828107839662016193 106576371080879746512145)
                ·
                  refine ⟨79932278310659809884109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106576371080879746512145 79932278310659809884109)
                  ·
                    refine ⟨29974604366497428706541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79932278310659809884109 29974604366497428706541)
                    ·
                      rfl

theorem cell22_87563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 2, 3].length) (baseStart_87563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87563 prefixEnd_87563 := by exact prefixLift 87563
  have htrace : WordTrace (prefixWord ++ tailWord_87563) baseStart_87563 baseEnd_87563 := by
    simpa [prefixWord, tailWord_87563, baseEnd_87563] using wordTrace_append hprefix tailTrace_87563
  have hstable : (prefixWord ++ tailWord_87563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87563).length < 2 ^ (prefixWord ++ tailWord_87563).sum := by decide
  have hdescent : baseEnd_87563 < baseStart_87563 := by decide
  rcases family_descends (prefixWord ++ tailWord_87563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87608 : List Nat := [2, 1, 2, 1, 4, 4, 1, 3, 1, 3]
def baseStart_87608 : Nat := 118140960795 + 87608 * 2 ^ 59
def prefixEnd_87608 : Nat := 4983230072969 + 3 ^ 40 * 87608 * 2
def baseEnd_87608 : Nat := 29990008786132311331403

theorem tailTrace_87608 : CollatzResearch.WordTrace tailWord_87608 prefixEnd_87608 29990008786132311331403 := by
  unfold tailWord_87608
  simp only [CollatzResearch.WordTrace]
  refine ⟨1597663133309326550151739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2130217511079102066868985 1597663133309326550151739)
  ·
    refine ⟨2396494699963989825227609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1597663133309326550151739 2396494699963989825227609)
    ·
      refine ⟨1797371024972992368920707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2396494699963989825227609 1797371024972992368920707)
      ·
        refine ⟨2696056537459488553381061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1797371024972992368920707 2696056537459488553381061)
        ·
          refine ⟨505510600773654103758949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2696056537459488553381061 505510600773654103758949)
          ·
            refine ⟨94783237645060144454803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 505510600773654103758949 94783237645060144454803)
            ·
              refine ⟨142174856467590216682205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94783237645060144454803 142174856467590216682205)
              ·
                refine ⟨53315571175346331255827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142174856467590216682205 53315571175346331255827)
                ·
                  refine ⟨79973356763019496883741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53315571175346331255827 79973356763019496883741)
                  ·
                    refine ⟨29990008786132311331403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 79973356763019496883741 29990008786132311331403)
                    ·
                      rfl

theorem cell22_87608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 3, 1, 3].length) (baseStart_87608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87608 prefixEnd_87608 := by exact prefixLift 87608
  have htrace : WordTrace (prefixWord ++ tailWord_87608) baseStart_87608 baseEnd_87608 := by
    simpa [prefixWord, tailWord_87608, baseEnd_87608] using wordTrace_append hprefix tailTrace_87608
  have hstable : (prefixWord ++ tailWord_87608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87608).length < 2 ^ (prefixWord ++ tailWord_87608).sum := by decide
  have hdescent : baseEnd_87608 < baseStart_87608 := by decide
  rcases family_descends (prefixWord ++ tailWord_87608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87651 : List Nat := [1, 1, 1, 5, 1, 5, 1, 2, 1, 4]
def baseStart_87651 : Nat := 118140960795 + 87651 * 2 ^ 59
def prefixEnd_87651 : Nat := 4983230072969 + 3 ^ 40 * 87651 * 2
def baseEnd_87651 : Nat := 30004728564894532506271

theorem tailTrace_87651 : CollatzResearch.WordTrace tailWord_87651 prefixEnd_87651 30004728564894532506271 := by
  unfold tailWord_87651
  simp only [CollatzResearch.WordTrace]
  refine ⟨3196894605462871444118807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2131263070308580962745871 3196894605462871444118807)
  ·
    refine ⟨4795341908194307166178211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3196894605462871444118807 4795341908194307166178211)
    ·
      refine ⟨7193012862291460749267317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4795341908194307166178211 7193012862291460749267317)
      ·
        refine ⟨674344955839824445243811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7193012862291460749267317 674344955839824445243811)
        ·
          refine ⟨1011517433759736667865717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 674344955839824445243811 1011517433759736667865717)
          ·
            refine ⟨94829759414975312612411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1011517433759736667865717 94829759414975312612411)
            ·
              refine ⟨142244639122462968918617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94829759414975312612411 142244639122462968918617)
              ·
                refine ⟨106683479341847226688963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142244639122462968918617 106683479341847226688963)
                ·
                  refine ⟨160025219012770840033445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106683479341847226688963 160025219012770840033445)
                  ·
                    refine ⟨30004728564894532506271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 160025219012770840033445 30004728564894532506271)
                    ·
                      rfl

theorem cell22_87651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 4].length) (baseStart_87651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87651 prefixEnd_87651 := by exact prefixLift 87651
  have htrace : WordTrace (prefixWord ++ tailWord_87651) baseStart_87651 baseEnd_87651 := by
    simpa [prefixWord, tailWord_87651, baseEnd_87651] using wordTrace_append hprefix tailTrace_87651
  have hstable : (prefixWord ++ tailWord_87651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87651).length < 2 ^ (prefixWord ++ tailWord_87651).sum := by decide
  have hdescent : baseEnd_87651 < baseStart_87651 := by decide
  rcases family_descends (prefixWord ++ tailWord_87651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87664 : List Nat := [2, 1, 1, 1, 6, 2, 1, 2, 1, 5]
def baseStart_87664 : Nat := 118140960795 + 87664 * 2 ^ 59
def prefixEnd_87664 : Nat := 4983230072969 + 3 ^ 40 * 87664 * 2
def baseEnd_87664 : Nat := 30009178730566831931231

theorem tailTrace_87664 : CollatzResearch.WordTrace tailWord_87664 prefixEnd_87664 30009178730566831931231 := by
  unfold tailWord_87664
  simp only [CollatzResearch.WordTrace]
  refine ⟨1598684377207887332171023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2131579169610516442894697 1598684377207887332171023)
  ·
    refine ⟨2398026565811830998256535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1598684377207887332171023 2398026565811830998256535)
    ·
      refine ⟨3597039848717746497384803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2398026565811830998256535 3597039848717746497384803)
      ·
        refine ⟨5395559773076619746077205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3597039848717746497384803 5395559773076619746077205)
        ·
          refine ⟨252916864362966550597369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5395559773076619746077205 252916864362966550597369)
          ·
            refine ⟨189687648272224912948027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252916864362966550597369 189687648272224912948027)
            ·
              refine ⟨284531472408337369422041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189687648272224912948027 284531472408337369422041)
              ·
                refine ⟨213398604306253027066531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 284531472408337369422041 213398604306253027066531)
                ·
                  refine ⟨320097906459379540599797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 213398604306253027066531 320097906459379540599797)
                  ·
                    refine ⟨30009178730566831931231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 320097906459379540599797 30009178730566831931231)
                    ·
                      rfl

theorem cell22_87664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 1, 5].length) (baseStart_87664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87664 prefixEnd_87664 := by exact prefixLift 87664
  have htrace : WordTrace (prefixWord ++ tailWord_87664) baseStart_87664 baseEnd_87664 := by
    simpa [prefixWord, tailWord_87664, baseEnd_87664] using wordTrace_append hprefix tailTrace_87664
  have hstable : (prefixWord ++ tailWord_87664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87664).length < 2 ^ (prefixWord ++ tailWord_87664).sum := by decide
  have hdescent : baseEnd_87664 < baseStart_87664 := by decide
  rcases family_descends (prefixWord ++ tailWord_87664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87677 : List Nat := [1, 4, 1, 1, 4, 11]
def baseStart_87677 : Nat := 118140960795 + 87677 * 2 ^ 59
def prefixEnd_87677 : Nat := 4983230072969 + 3 ^ 40 * 87677 * 2
def baseEnd_87677 : Nat := 370538628348631251311

theorem tailTrace_87677 : CollatzResearch.WordTrace tailWord_87677 prefixEnd_87677 370538628348631251311 := by
  unfold tailWord_87677
  simp only [CollatzResearch.WordTrace]
  refine ⟨3197842903368677884565285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2131895268912451923043523 3197842903368677884565285)
  ·
    refine ⟨599595544381627103355991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3197842903368677884565285 599595544381627103355991)
    ·
      refine ⟨899393316572440655033987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 599595544381627103355991 899393316572440655033987)
      ·
        refine ⟨1349089974858660982550981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 899393316572440655033987 1349089974858660982550981)
        ·
          refine ⟨252954370285998934228309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1349089974858660982550981 252954370285998934228309)
          ·
            refine ⟨370538628348631251311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 252954370285998934228309 370538628348631251311)
            ·
              rfl

theorem cell22_87677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 11].length) (baseStart_87677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87677 prefixEnd_87677 := by exact prefixLift 87677
  have htrace : WordTrace (prefixWord ++ tailWord_87677) baseStart_87677 baseEnd_87677 := by
    simpa [prefixWord, tailWord_87677, baseEnd_87677] using wordTrace_append hprefix tailTrace_87677
  have hstable : (prefixWord ++ tailWord_87677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87677).length < 2 ^ (prefixWord ++ tailWord_87677).sum := by decide
  have hdescent : baseEnd_87677 < baseStart_87677 := by decide
  rcases family_descends (prefixWord ++ tailWord_87677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87681 : List Nat := [1, 2, 4, 2, 1, 2, 1, 4, 2, 3]
def baseStart_87681 : Nat := 118140960795 + 87681 * 2 ^ 59
def prefixEnd_87681 : Nat := 4983230072969 + 3 ^ 40 * 87681 * 2
def baseEnd_87681 : Nat := 30014998177984454256179

theorem tailTrace_87681 : CollatzResearch.WordTrace tailWord_87681 prefixEnd_87681 30014998177984454256179 := by
  unfold tailWord_87681
  simp only [CollatzResearch.WordTrace]
  refine ⟨3197988795354186567710897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2131992530236124378473931 3197988795354186567710897)
  ·
    refine ⟨2398491596515639925783173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3197988795354186567710897 2398491596515639925783173)
    ·
      refine ⟨449717174346682486084345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2398491596515639925783173 449717174346682486084345)
      ·
        refine ⟨337287880760011864563259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 449717174346682486084345 337287880760011864563259)
        ·
          refine ⟨505931821140017796844889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337287880760011864563259 505931821140017796844889)
          ·
            refine ⟨379448865855013347633667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 505931821140017796844889 379448865855013347633667)
            ·
              refine ⟨569173298782520021450501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 379448865855013347633667 569173298782520021450501)
              ·
                refine ⟨106719993521722504021969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 569173298782520021450501 106719993521722504021969)
                ·
                  refine ⟨80039995141291878016477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106719993521722504021969 80039995141291878016477)
                  ·
                    refine ⟨30014998177984454256179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 80039995141291878016477 30014998177984454256179)
                    ·
                      rfl

theorem cell22_87681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_87681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87681 prefixEnd_87681 := by exact prefixLift 87681
  have htrace : WordTrace (prefixWord ++ tailWord_87681) baseStart_87681 baseEnd_87681 := by
    simpa [prefixWord, tailWord_87681, baseEnd_87681] using wordTrace_append hprefix tailTrace_87681
  have hstable : (prefixWord ++ tailWord_87681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87681).length < 2 ^ (prefixWord ++ tailWord_87681).sum := by decide
  have hdescent : baseEnd_87681 < baseStart_87681 := by decide
  rcases family_descends (prefixWord ++ tailWord_87681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87694 : List Nat := [4, 1, 1, 3, 1, 2, 3, 7]
def baseStart_87694 : Nat := 118140960795 + 87694 * 2 ^ 59
def prefixEnd_87694 : Nat := 4983230072969 + 3 ^ 40 * 87694 * 2
def baseEnd_87694 : Nat := 3335494260406305964571

theorem tailTrace_87694 : CollatzResearch.WordTrace tailWord_87694 prefixEnd_87694 3335494260406305964571 := by
  unfold tailWord_87694
  simp only [CollatzResearch.WordTrace]
  refine ⟨399807868038386223491767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2132308629538059858622757 399807868038386223491767)
  ·
    refine ⟨599711802057579335237651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 399807868038386223491767 599711802057579335237651)
    ·
      refine ⟨899567703086369002856477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 599711802057579335237651 899567703086369002856477)
      ·
        refine ⟨337337888657388376071179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 899567703086369002856477 337337888657388376071179)
        ·
          refine ⟨506006832986082564106769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337337888657388376071179 506006832986082564106769)
          ·
            refine ⟨379505124739561923080077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 506006832986082564106769 379505124739561923080077)
            ·
              refine ⟨142314421777335721155029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 379505124739561923080077 142314421777335721155029)
              ·
                refine ⟨3335494260406305964571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 142314421777335721155029 3335494260406305964571)
                ·
                  rfl

theorem cell22_87694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 7].length) (baseStart_87694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87694 prefixEnd_87694 := by exact prefixLift 87694
  have htrace : WordTrace (prefixWord ++ tailWord_87694) baseStart_87694 baseEnd_87694 := by
    simpa [prefixWord, tailWord_87694, baseEnd_87694] using wordTrace_append hprefix tailTrace_87694
  have hstable : (prefixWord ++ tailWord_87694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87694).length < 2 ^ (prefixWord ++ tailWord_87694).sum := by decide
  have hdescent : baseEnd_87694 < baseStart_87694 := by decide
  rcases family_descends (prefixWord ++ tailWord_87694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87777 : List Nat := [1, 2, 3, 1, 6, 1, 1, 3, 1, 3]
def baseStart_87777 : Nat := 118140960795 + 87777 * 2 ^ 59
def prefixEnd_87777 : Nat := 4983230072969 + 3 ^ 40 * 87777 * 2
def baseEnd_87777 : Nat := 30047860939872203855885

theorem tailTrace_87777 : CollatzResearch.WordTrace tailWord_87777 prefixEnd_87777 30047860939872203855885 := by
  unfold tailWord_87777
  simp only [CollatzResearch.WordTrace]
  refine ⟨3201490203006394963205585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2134326802004263308803723 3201490203006394963205585)
  ·
    refine ⟨2401117652254796222404189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3201490203006394963205585 2401117652254796222404189)
    ·
      refine ⟨900419119595548583401571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2401117652254796222404189 900419119595548583401571)
      ·
        refine ⟨1350628679393322875102357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 900419119595548583401571 1350628679393322875102357)
        ·
          refine ⟨63310719346562009770423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1350628679393322875102357 63310719346562009770423)
          ·
            refine ⟨94966079019843014655635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63310719346562009770423 94966079019843014655635)
            ·
              refine ⟨142449118529764521983453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94966079019843014655635 142449118529764521983453)
              ·
                refine ⟨53418419448661695743795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142449118529764521983453 53418419448661695743795)
                ·
                  refine ⟨80127629172992543615693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53418419448661695743795 80127629172992543615693)
                  ·
                    refine ⟨30047860939872203855885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 80127629172992543615693 30047860939872203855885)
                    ·
                      rfl

theorem cell22_87777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 3, 1, 3].length) (baseStart_87777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87777 prefixEnd_87777 := by exact prefixLift 87777
  have htrace : WordTrace (prefixWord ++ tailWord_87777) baseStart_87777 baseEnd_87777 := by
    simpa [prefixWord, tailWord_87777, baseEnd_87777] using wordTrace_append hprefix tailTrace_87777
  have hstable : (prefixWord ++ tailWord_87777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87777).length < 2 ^ (prefixWord ++ tailWord_87777).sum := by decide
  have hdescent : baseEnd_87777 < baseStart_87777 := by decide
  rcases family_descends (prefixWord ++ tailWord_87777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87786 : List Nat := [3, 1, 3, 1, 1, 1, 4, 3, 1, 4]
def baseStart_87786 : Nat := 118140960795 + 87786 * 2 ^ 59
def prefixEnd_87786 : Nat := 4983230072969 + 3 ^ 40 * 87786 * 2
def baseEnd_87786 : Nat := 30050941823799180380857

theorem tailTrace_87786 : CollatzResearch.WordTrace tailWord_87786 prefixEnd_87786 30050941823799180380857 := by
  unfold tailWord_87786
  simp only [CollatzResearch.WordTrace]
  refine ⟨800454614993447375070803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2134545639982526333522141 800454614993447375070803)
  ·
    refine ⟨1200681922490171062606205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 800454614993447375070803 1200681922490171062606205)
    ·
      refine ⟨450255720933814148477327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1200681922490171062606205 450255720933814148477327)
      ·
        refine ⟨675383581400721222715991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450255720933814148477327 675383581400721222715991)
        ·
          refine ⟨1013075372101081834073987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 675383581400721222715991 1013075372101081834073987)
          ·
            refine ⟨1519613058151622751110981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1013075372101081834073987 1519613058151622751110981)
            ·
              refine ⟨284927448403429265833309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1519613058151622751110981 284927448403429265833309)
              ·
                refine ⟨106847793151285974687491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 284927448403429265833309 106847793151285974687491)
                ·
                  refine ⟨160271689726928962031237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106847793151285974687491 160271689726928962031237)
                  ·
                    refine ⟨30050941823799180380857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 160271689726928962031237 30050941823799180380857)
                    ·
                      rfl

theorem cell22_87786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_87786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87786 prefixEnd_87786 := by exact prefixLift 87786
  have htrace : WordTrace (prefixWord ++ tailWord_87786) baseStart_87786 baseEnd_87786 := by
    simpa [prefixWord, tailWord_87786, baseEnd_87786] using wordTrace_append hprefix tailTrace_87786
  have hstable : (prefixWord ++ tailWord_87786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87786).length < 2 ^ (prefixWord ++ tailWord_87786).sum := by decide
  have hdescent : baseEnd_87786 < baseStart_87786 := by decide
  rcases family_descends (prefixWord ++ tailWord_87786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87829 : List Nat := [1, 3, 2, 1, 2, 3, 2, 8]
def baseStart_87829 : Nat := 118140960795 + 87829 * 2 ^ 59
def prefixEnd_87829 : Nat := 4983230072969 + 3 ^ 40 * 87829 * 2
def baseEnd_87829 : Nat := 3340629066951266839525

theorem tailTrace_87829 : CollatzResearch.WordTrace tailWord_87829 prefixEnd_87829 3340629066951266839525 := by
  unfold tailWord_87829
  simp only [CollatzResearch.WordTrace]
  refine ⟨3203386798818007844098541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2135591199212005229399027 3203386798818007844098541)
  ·
    refine ⟨1201270049556752941536953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3203386798818007844098541 1201270049556752941536953)
    ·
      refine ⟨900952537167564706152715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1201270049556752941536953 900952537167564706152715)
      ·
        refine ⟨1351428805751347059229073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 900952537167564706152715 1351428805751347059229073)
        ·
          refine ⟨1013571604313510294421805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1351428805751347059229073 1013571604313510294421805)
          ·
            refine ⟨380089351617566360408177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1013571604313510294421805 380089351617566360408177)
            ·
              refine ⟨285067013713174770306133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 380089351617566360408177 285067013713174770306133)
              ·
                refine ⟨3340629066951266839525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 285067013713174770306133 3340629066951266839525)
                ·
                  rfl

theorem cell22_87829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 8].length) (baseStart_87829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87829 prefixEnd_87829 := by exact prefixLift 87829
  have htrace : WordTrace (prefixWord ++ tailWord_87829) baseStart_87829 baseEnd_87829 := by
    simpa [prefixWord, tailWord_87829, baseEnd_87829] using wordTrace_append hprefix tailTrace_87829
  have hstable : (prefixWord ++ tailWord_87829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87829).length < 2 ^ (prefixWord ++ tailWord_87829).sum := by decide
  have hdescent : baseEnd_87829 < baseStart_87829 := by decide
  rcases family_descends (prefixWord ++ tailWord_87829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87831 : List Nat := [1, 1, 3, 4, 2, 1, 1, 3, 2, 4]
def baseStart_87831 : Nat := 118140960795 + 87831 * 2 ^ 59
def prefixEnd_87831 : Nat := 4983230072969 + 3 ^ 40 * 87831 * 2
def baseEnd_87831 : Nat := 30066346243434063005719

theorem tailTrace_87831 : CollatzResearch.WordTrace tailWord_87831 prefixEnd_87831 30066346243434063005719 := by
  unfold tailWord_87831
  simp only [CollatzResearch.WordTrace]
  refine ⟨3203459744810762185671347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2135639829873841457114231 3203459744810762185671347)
  ·
    refine ⟨4805189617216143278507021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3203459744810762185671347 4805189617216143278507021)
    ·
      refine ⟨1801946106456053729440133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4805189617216143278507021 1801946106456053729440133)
      ·
        refine ⟨337864894960510074270025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1801946106456053729440133 337864894960510074270025)
        ·
          refine ⟨253398671220382555702519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337864894960510074270025 253398671220382555702519)
          ·
            refine ⟨380098006830573833553779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253398671220382555702519 380098006830573833553779)
            ·
              refine ⟨570147010245860750330669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 380098006830573833553779 570147010245860750330669)
              ·
                refine ⟨213805128842197781374001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 570147010245860750330669 213805128842197781374001)
                ·
                  refine ⟨160353846631648336030501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213805128842197781374001 160353846631648336030501)
                  ·
                    refine ⟨30066346243434063005719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 160353846631648336030501 30066346243434063005719)
                    ·
                      rfl

theorem cell22_87831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 4].length) (baseStart_87831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87831 prefixEnd_87831 := by exact prefixLift 87831
  have htrace : WordTrace (prefixWord ++ tailWord_87831) baseStart_87831 baseEnd_87831 := by
    simpa [prefixWord, tailWord_87831, baseEnd_87831] using wordTrace_append hprefix tailTrace_87831
  have hstable : (prefixWord ++ tailWord_87831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87831).length < 2 ^ (prefixWord ++ tailWord_87831).sum := by decide
  have hdescent : baseEnd_87831 < baseStart_87831 := by decide
  rcases family_descends (prefixWord ++ tailWord_87831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87953 : List Nat := [1, 2, 2, 1, 1, 1, 7, 3, 4]
def baseStart_87953 : Nat := 118140960795 + 87953 * 2 ^ 59
def prefixEnd_87953 : Nat := 4983230072969 + 3 ^ 40 * 87953 * 2
def baseEnd_87953 : Nat := 10036036445555470485115

theorem tailTrace_87953 : CollatzResearch.WordTrace tailWord_87953 prefixEnd_87953 10036036445555470485115 := by
  unfold tailWord_87953
  simp only [CollatzResearch.WordTrace]
  refine ⟨3207909450368777021612513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2138606300245851347741675 3207909450368777021612513)
  ·
    refine ⟨2405932087776582766209385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3207909450368777021612513 2405932087776582766209385)
    ·
      refine ⟨1804449065832437074657039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2405932087776582766209385 1804449065832437074657039)
      ·
        refine ⟨2706673598748655611985559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1804449065832437074657039 2706673598748655611985559)
        ·
          refine ⟨4060010398122983417978339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2706673598748655611985559 4060010398122983417978339)
          ·
            refine ⟨6090015597184475126967509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4060010398122983417978339 6090015597184475126967509)
            ·
              refine ⟨142734740559011135788301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 6090015597184475126967509 142734740559011135788301)
              ·
                refine ⟨53525527709629175920613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142734740559011135788301 53525527709629175920613)
                ·
                  refine ⟨10036036445555470485115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53525527709629175920613 10036036445555470485115)
                  ·
                    rfl

theorem cell22_87953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 3, 4].length) (baseStart_87953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87953 prefixEnd_87953 := by exact prefixLift 87953
  have htrace : WordTrace (prefixWord ++ tailWord_87953) baseStart_87953 baseEnd_87953 := by
    simpa [prefixWord, tailWord_87953, baseEnd_87953] using wordTrace_append hprefix tailTrace_87953
  have hstable : (prefixWord ++ tailWord_87953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87953).length < 2 ^ (prefixWord ++ tailWord_87953).sum := by decide
  have hdescent : baseEnd_87953 < baseStart_87953 := by decide
  rcases family_descends (prefixWord ++ tailWord_87953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87968 : List Nat := [2, 1, 1, 4, 1, 1, 1, 6, 2, 3]
def baseStart_87968 : Nat := 118140960795 + 87968 * 2 ^ 59
def prefixEnd_87968 : Nat := 4983230072969 + 3 ^ 40 * 87968 * 2
def baseEnd_87968 : Nat := 30113244143211372330299

theorem tailTrace_87968 : CollatzResearch.WordTrace tailWord_87968 prefixEnd_87968 30113244143211372330299 := by
  unfold tailWord_87968
  simp only [CollatzResearch.WordTrace]
  refine ⟨1604228272657217291704279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2138971030209623055605705 1604228272657217291704279)
  ·
    refine ⟨2406342408985825937556419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1604228272657217291704279 2406342408985825937556419)
    ·
      refine ⟨3609513613478738906334629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2406342408985825937556419 3609513613478738906334629)
      ·
        refine ⟨676783802527263544937743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3609513613478738906334629 676783802527263544937743)
        ·
          refine ⟨1015175703790895317406615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 676783802527263544937743 1015175703790895317406615)
          ·
            refine ⟨1522763555686342976109923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1015175703790895317406615 1522763555686342976109923)
            ·
              refine ⟨2284145333529514464164885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1522763555686342976109923 2284145333529514464164885)
              ·
                refine ⟨107069312509195990507729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2284145333529514464164885 107069312509195990507729)
                ·
                  refine ⟨80301984381896992880797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107069312509195990507729 80301984381896992880797)
                  ·
                    refine ⟨30113244143211372330299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 80301984381896992880797 30113244143211372330299)
                    ·
                      rfl

theorem cell22_87968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 2, 3].length) (baseStart_87968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87968 prefixEnd_87968 := by exact prefixLift 87968
  have htrace : WordTrace (prefixWord ++ tailWord_87968) baseStart_87968 baseEnd_87968 := by
    simpa [prefixWord, tailWord_87968, baseEnd_87968] using wordTrace_append hprefix tailTrace_87968
  have hstable : (prefixWord ++ tailWord_87968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87968).length < 2 ^ (prefixWord ++ tailWord_87968).sum := by decide
  have hdescent : baseEnd_87968 < baseStart_87968 := by decide
  rcases family_descends (prefixWord ++ tailWord_87968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87970 : List Nat := [3, 3, 1, 2, 3, 2, 1, 1, 6]
def baseStart_87970 : Nat := 118140960795 + 87970 * 2 ^ 59
def prefixEnd_87970 : Nat := 4983230072969 + 3 ^ 40 * 87970 * 2
def baseEnd_87970 : Nat := 10037976261361344593431

theorem tailTrace_87970 : CollatzResearch.WordTrace tailWord_87970 prefixEnd_87970 10037976261361344593431 := by
  unfold tailWord_87970
  simp only [CollatzResearch.WordTrace]
  refine ⟨802132372826797231245341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2139019660871459283320909 802132372826797231245341)
  ·
    refine ⟨300799639810048961717003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 802132372826797231245341 300799639810048961717003)
    ·
      refine ⟨451199459715073442575505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300799639810048961717003 451199459715073442575505)
      ·
        refine ⟨338399594786305081931629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 451199459715073442575505 338399594786305081931629)
        ·
          refine ⟨126899848044864405724361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 338399594786305081931629 126899848044864405724361)
          ·
            refine ⟨95174886033648304293271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126899848044864405724361 95174886033648304293271)
            ·
              refine ⟨142762329050472456439907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95174886033648304293271 142762329050472456439907)
              ·
                refine ⟨214143493575708684659861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142762329050472456439907 214143493575708684659861)
                ·
                  refine ⟨10037976261361344593431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 214143493575708684659861 10037976261361344593431)
                  ·
                    rfl

theorem cell22_87970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_87970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87970 prefixEnd_87970 := by exact prefixLift 87970
  have htrace : WordTrace (prefixWord ++ tailWord_87970) baseStart_87970 baseEnd_87970 := by
    simpa [prefixWord, tailWord_87970, baseEnd_87970] using wordTrace_append hprefix tailTrace_87970
  have hstable : (prefixWord ++ tailWord_87970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87970).length < 2 ^ (prefixWord ++ tailWord_87970).sum := by decide
  have hdescent : baseEnd_87970 < baseStart_87970 := by decide
  rcases family_descends (prefixWord ++ tailWord_87970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87985 : List Nat := [1, 2, 2, 4, 2, 2, 1, 3, 2, 3]
def baseStart_87985 : Nat := 118140960795 + 87985 * 2 ^ 59
def prefixEnd_87985 : Nat := 4983230072969 + 3 ^ 40 * 87985 * 2
def baseEnd_87985 : Nat := 30119063590628994655247

theorem tailTrace_87985 : CollatzResearch.WordTrace tailWord_87985 prefixEnd_87985 30119063590628994655247 := by
  unfold tailWord_87985
  simp only [CollatzResearch.WordTrace]
  refine ⟨3209076586252846486777409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2139384390835230991184939 3209076586252846486777409)
  ·
    refine ⟨2406807439689634865083057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3209076586252846486777409 2406807439689634865083057)
    ·
      refine ⟨1805105579767226148812293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2406807439689634865083057 1805105579767226148812293)
      ·
        refine ⟨338457296206354902902305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1805105579767226148812293 338457296206354902902305)
        ·
          refine ⟨253842972154766177176729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 338457296206354902902305 253842972154766177176729)
          ·
            refine ⟨190382229116074632882547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253842972154766177176729 190382229116074632882547)
            ·
              refine ⟨285573343674111949323821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190382229116074632882547 285573343674111949323821)
              ·
                refine ⟨107090003877791980996433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 285573343674111949323821 107090003877791980996433)
                ·
                  refine ⟨80317502908343985747325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107090003877791980996433 80317502908343985747325)
                  ·
                    refine ⟨30119063590628994655247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 80317502908343985747325 30119063590628994655247)
                    ·
                      rfl

theorem cell22_87985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 2, 3].length) (baseStart_87985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_87985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_87985 prefixEnd_87985 := by exact prefixLift 87985
  have htrace : WordTrace (prefixWord ++ tailWord_87985) baseStart_87985 baseEnd_87985 := by
    simpa [prefixWord, tailWord_87985, baseEnd_87985] using wordTrace_append hprefix tailTrace_87985
  have hstable : (prefixWord ++ tailWord_87985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87985).length < 2 ^ (prefixWord ++ tailWord_87985).sum := by decide
  have hdescent : baseEnd_87985 < baseStart_87985 := by decide
  rcases family_descends (prefixWord ++ tailWord_87985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88070 : List Nat := [6, 2, 1, 2, 2, 1, 1, 2, 2, 3]
def baseStart_88070 : Nat := 118140960795 + 88070 * 2 ^ 59
def prefixEnd_88070 : Nat := 4983230072969 + 3 ^ 40 * 88070 * 2
def baseEnd_88070 : Nat := 30148160827717106279987

theorem tailTrace_88070 : CollatzResearch.WordTrace tailWord_88070 prefixEnd_88070 30148160827717106279987 := by
  unfold tailWord_88070
  simp only [CollatzResearch.WordTrace]
  refine ⟨100380524717028312613177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2141451193963270669081109 100380524717028312613177)
  ·
    refine ⟨75285393537771234459883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 100380524717028312613177 75285393537771234459883)
    ·
      refine ⟨112928090306656851689825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75285393537771234459883 112928090306656851689825)
      ·
        refine ⟨84696067729992638767369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112928090306656851689825 84696067729992638767369)
        ·
          refine ⟨63522050797494479075527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84696067729992638767369 63522050797494479075527)
          ·
            refine ⟨95283076196241718613291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63522050797494479075527 95283076196241718613291)
            ·
              refine ⟨142924614294362577919937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95283076196241718613291 142924614294362577919937)
              ·
                refine ⟨107193460720771933439953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142924614294362577919937 107193460720771933439953)
                ·
                  refine ⟨80395095540578950079965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 107193460720771933439953 80395095540578950079965)
                  ·
                    refine ⟨30148160827717106279987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 80395095540578950079965 30148160827717106279987)
                    ·
                      rfl

theorem cell22_88070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_88070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_88070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_88070 prefixEnd_88070 := by exact prefixLift 88070
  have htrace : WordTrace (prefixWord ++ tailWord_88070) baseStart_88070 baseEnd_88070 := by
    simpa [prefixWord, tailWord_88070, baseEnd_88070] using wordTrace_append hprefix tailTrace_88070
  have hstable : (prefixWord ++ tailWord_88070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88070).length < 2 ^ (prefixWord ++ tailWord_88070).sum := by decide
  have hdescent : baseEnd_88070 < baseStart_88070 := by decide
  rcases family_descends (prefixWord ++ tailWord_88070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88088 : List Nat := [2, 1, 2, 3, 2, 1, 4, 1, 6]
def baseStart_88088 : Nat := 118140960795 + 88088 * 2 ^ 59
def prefixEnd_88088 : Nat := 4983230072969 + 3 ^ 40 * 88088 * 2
def baseEnd_88088 : Nat := 10051440865190353109977

theorem tailTrace_88088 : CollatzResearch.WordTrace tailWord_88088 prefixEnd_88088 10051440865190353109977 := by
  unfold tailWord_88088
  simp only [CollatzResearch.WordTrace]
  refine ⟨1606416652439847538888459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2141888869919796718517945 1606416652439847538888459)
  ·
    refine ⟨2409624978659771308332689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1606416652439847538888459 2409624978659771308332689)
    ·
      refine ⟨1807218733994828481249517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2409624978659771308332689 1807218733994828481249517)
      ·
        refine ⟨677707025248060680468569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1807218733994828481249517 677707025248060680468569)
        ·
          refine ⟨508280268936045510351427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 677707025248060680468569 508280268936045510351427)
          ·
            refine ⟨762420403404068265527141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 508280268936045510351427 762420403404068265527141)
            ·
              refine ⟨142953825638262799786339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 762420403404068265527141 142953825638262799786339)
              ·
                refine ⟨214430738457394199679509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142953825638262799786339 214430738457394199679509)
                ·
                  refine ⟨10051440865190353109977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 214430738457394199679509 10051440865190353109977)
                  ·
                    rfl

theorem cell22_88088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 6].length) (baseStart_88088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_88088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_88088 prefixEnd_88088 := by exact prefixLift 88088
  have htrace : WordTrace (prefixWord ++ tailWord_88088) baseStart_88088 baseEnd_88088 := by
    simpa [prefixWord, tailWord_88088, baseEnd_88088] using wordTrace_append hprefix tailTrace_88088
  have hstable : (prefixWord ++ tailWord_88088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88088).length < 2 ^ (prefixWord ++ tailWord_88088).sum := by decide
  have hdescent : baseEnd_88088 < baseStart_88088 := by decide
  rcases family_descends (prefixWord ++ tailWord_88088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88158 : List Nat := [4, 4, 1, 1, 3, 1, 1, 2, 1, 4]
def baseStart_88158 : Nat := 118140960795 + 88158 * 2 ^ 59
def prefixEnd_88158 : Nat := 4983230072969 + 3 ^ 40 * 88158 * 2
def baseEnd_88158 : Nat := 30178285026114210079717

theorem tailTrace_88158 : CollatzResearch.WordTrace tailWord_88158 prefixEnd_88158 30178285026114210079717 := by
  unfold tailWord_88158
  simp only [CollatzResearch.WordTrace]
  refine ⟨401923301828262129103141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2143590943084064688550085 401923301828262129103141)
  ·
    refine ⟨75360619092799149206839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 401923301828262129103141 75360619092799149206839)
    ·
      refine ⟨113040928639198723810259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75360619092799149206839 113040928639198723810259)
      ·
        refine ⟨169561392958798085715389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113040928639198723810259 169561392958798085715389)
        ·
          refine ⟨63585522359549282143271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 169561392958798085715389 63585522359549282143271)
          ·
            refine ⟨95378283539323923214907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63585522359549282143271 95378283539323923214907)
            ·
              refine ⟨143067425308985884822361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95378283539323923214907 143067425308985884822361)
              ·
                refine ⟨107300568981739413616771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143067425308985884822361 107300568981739413616771)
                ·
                  refine ⟨160950853472609120425157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107300568981739413616771 160950853472609120425157)
                  ·
                    refine ⟨30178285026114210079717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 160950853472609120425157 30178285026114210079717)
                    ·
                      rfl

theorem cell22_88158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_88158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_88158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_88158 prefixEnd_88158 := by exact prefixLift 88158
  have htrace : WordTrace (prefixWord ++ tailWord_88158) baseStart_88158 baseEnd_88158 := by
    simpa [prefixWord, tailWord_88158, baseEnd_88158] using wordTrace_append hprefix tailTrace_88158
  have hstable : (prefixWord ++ tailWord_88158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88158).length < 2 ^ (prefixWord ++ tailWord_88158).sum := by decide
  have hdescent : baseEnd_88158 < baseStart_88158 := by decide
  rcases family_descends (prefixWord ++ tailWord_88158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88195 : List Nat := [1, 1, 1, 3, 3, 4, 2, 2, 5]
def baseStart_88195 : Nat := 118140960795 + 88195 * 2 ^ 59
def prefixEnd_88195 : Nat := 4983230072969 + 3 ^ 40 * 88195 * 2
def baseEnd_88195 : Nat := 10063650294086148968201

theorem tailTrace_88195 : CollatzResearch.WordTrace tailWord_88195 prefixEnd_88195 10063650294086148968201 := by
  unfold tailWord_88195
  simp only [CollatzResearch.WordTrace]
  refine ⟨3216735915492052351922039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2144490610328034901281359 3216735915492052351922039)
  ·
    refine ⟨4825103873238078527883059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3216735915492052351922039 4825103873238078527883059)
    ·
      refine ⟨7237655809857117791824589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4825103873238078527883059 7237655809857117791824589)
      ·
        refine ⟨2714120928696419171934221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7237655809857117791824589 2714120928696419171934221)
        ·
          refine ⟨1017795348261157189475333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2714120928696419171934221 1017795348261157189475333)
          ·
            refine ⟨190836627798966973026625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1017795348261157189475333 190836627798966973026625)
            ·
              refine ⟨143127470849225229769969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190836627798966973026625 143127470849225229769969)
              ·
                refine ⟨107345603136918922327477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143127470849225229769969 107345603136918922327477)
                ·
                  refine ⟨10063650294086148968201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 107345603136918922327477 10063650294086148968201)
                  ·
                    rfl

theorem cell22_88195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 5].length) (baseStart_88195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_88195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_88195 prefixEnd_88195 := by exact prefixLift 88195
  have htrace : WordTrace (prefixWord ++ tailWord_88195) baseStart_88195 baseEnd_88195 := by
    simpa [prefixWord, tailWord_88195, baseEnd_88195] using wordTrace_append hprefix tailTrace_88195
  have hstable : (prefixWord ++ tailWord_88195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88195).length < 2 ^ (prefixWord ++ tailWord_88195).sum := by decide
  have hdescent : baseEnd_88195 < baseStart_88195 := by decide
  rcases family_descends (prefixWord ++ tailWord_88195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88199 : List Nat := [1, 1, 4, 2, 1, 1, 6, 2, 1, 3]
def baseStart_88199 : Nat := 118140960795 + 88199 * 2 ^ 59
def prefixEnd_88199 : Nat := 4983230072969 + 3 ^ 40 * 88199 * 2
def baseEnd_88199 : Nat := 30192320164003769804591

theorem tailTrace_88199 : CollatzResearch.WordTrace tailWord_88199 prefixEnd_88199 30192320164003769804591 := by
  unfold tailWord_88199
  simp only [CollatzResearch.WordTrace]
  refine ⟨3216881807477561035067651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2144587871651707356711767 3216881807477561035067651)
  ·
    refine ⟨4825322711216341552601477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3216881807477561035067651 4825322711216341552601477)
    ·
      refine ⟨904748008353064041112777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4825322711216341552601477 904748008353064041112777)
      ·
        refine ⟨678561006264798030834583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 904748008353064041112777 678561006264798030834583)
        ·
          refine ⟨1017841509397197046251875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 678561006264798030834583 1017841509397197046251875)
          ·
            refine ⟨1526762264095795569377813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1017841509397197046251875 1526762264095795569377813)
            ·
              refine ⟨71566981129490417314585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1526762264095795569377813 71566981129490417314585)
              ·
                refine ⟨53675235847117812985939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71566981129490417314585 53675235847117812985939)
                ·
                  refine ⟨80512853770676719478909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53675235847117812985939 80512853770676719478909)
                  ·
                    refine ⟨30192320164003769804591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 80512853770676719478909 30192320164003769804591)
                    ·
                      rfl

theorem cell22_88199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 2, 1, 3].length) (baseStart_88199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_88199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_88199 prefixEnd_88199 := by exact prefixLift 88199
  have htrace : WordTrace (prefixWord ++ tailWord_88199) baseStart_88199 baseEnd_88199 := by
    simpa [prefixWord, tailWord_88199, baseEnd_88199] using wordTrace_append hprefix tailTrace_88199
  have hstable : (prefixWord ++ tailWord_88199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88199).length < 2 ^ (prefixWord ++ tailWord_88199).sum := by decide
  have hdescent : baseEnd_88199 < baseStart_88199 := by decide
  rcases family_descends (prefixWord ++ tailWord_88199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88208 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 5, 4]
def baseStart_88208 : Nat := 118140960795 + 88208 * 2 ^ 59
def prefixEnd_88208 : Nat := 4983230072969 + 3 ^ 40 * 88208 * 2
def baseEnd_88208 : Nat := 30195401047930746329563

theorem tailTrace_88208 : CollatzResearch.WordTrace tailWord_88208 prefixEnd_88208 30195401047930746329563 := by
  unfold tailWord_88208
  simp only [CollatzResearch.WordTrace]
  refine ⟨1608605032222477786072639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2144806709629970381430185 1608605032222477786072639)
  ·
    refine ⟨2412907548333716679108959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1608605032222477786072639 2412907548333716679108959)
    ·
      refine ⟨3619361322500575018663439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2412907548333716679108959 3619361322500575018663439)
      ·
        refine ⟨5429041983750862527995159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3619361322500575018663439 5429041983750862527995159)
        ·
          refine ⟨8143562975626293791992739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5429041983750862527995159 8143562975626293791992739)
          ·
            refine ⟨12215344463439440687989109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8143562975626293791992739 12215344463439440687989109)
            ·
              refine ⟨1145188543447447564498979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12215344463439440687989109 1145188543447447564498979)
              ·
                refine ⟨1717782815171171346748469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1145188543447447564498979 1717782815171171346748469)
                ·
                  refine ⟨161042138922297313757669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1717782815171171346748469 161042138922297313757669)
                  ·
                    refine ⟨30195401047930746329563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 161042138922297313757669 30195401047930746329563)
                    ·
                      rfl

theorem cell22_88208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 5, 4].length) (baseStart_88208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_88208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_88208 prefixEnd_88208 := by exact prefixLift 88208
  have htrace : WordTrace (prefixWord ++ tailWord_88208) baseStart_88208 baseEnd_88208 := by
    simpa [prefixWord, tailWord_88208, baseEnd_88208] using wordTrace_append hprefix tailTrace_88208
  have hstable : (prefixWord ++ tailWord_88208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88208).length < 2 ^ (prefixWord ++ tailWord_88208).sum := by decide
  have hdescent : baseEnd_88208 < baseStart_88208 := by decide
  rcases family_descends (prefixWord ++ tailWord_88208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88210 : List Nat := [3, 2, 3, 1, 1, 1, 3, 1, 2, 5]
def baseStart_88210 : Nat := 118140960795 + 88210 * 2 ^ 59
def prefixEnd_88210 : Nat := 4983230072969 + 3 ^ 40 * 88210 * 2
def baseEnd_88210 : Nat := 30196085688803407779557

theorem tailTrace_88210 : CollatzResearch.WordTrace tailWord_88210 prefixEnd_88210 30196085688803407779557 := by
  unfold tailWord_88210
  simp only [CollatzResearch.WordTrace]
  refine ⟨804320752609427478429521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2144855340291806609145389 804320752609427478429521)
  ·
    refine ⟨603240564457070608822141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 804320752609427478429521 603240564457070608822141)
    ·
      refine ⟨226215211671401478308303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 603240564457070608822141 226215211671401478308303)
      ·
        refine ⟨339322817507102217462455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226215211671401478308303 339322817507102217462455)
        ·
          refine ⟨508984226260653326193683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339322817507102217462455 508984226260653326193683)
          ·
            refine ⟨763476339390979989290525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 508984226260653326193683 763476339390979989290525)
            ·
              refine ⟨286303627271617495983947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 763476339390979989290525 286303627271617495983947)
              ·
                refine ⟨429455440907426243975921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 286303627271617495983947 429455440907426243975921)
                ·
                  refine ⟨322091580680569682981941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 429455440907426243975921 322091580680569682981941)
                  ·
                    refine ⟨30196085688803407779557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 322091580680569682981941 30196085688803407779557)
                    ·
                      rfl

theorem cell22_88210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_88210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_88210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_88210 prefixEnd_88210 := by exact prefixLift 88210
  have htrace : WordTrace (prefixWord ++ tailWord_88210) baseStart_88210 baseEnd_88210 := by
    simpa [prefixWord, tailWord_88210, baseEnd_88210] using wordTrace_append hprefix tailTrace_88210
  have hstable : (prefixWord ++ tailWord_88210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88210).length < 2 ^ (prefixWord ++ tailWord_88210).sum := by decide
  have hdescent : baseEnd_88210 < baseStart_88210 := by decide
  rcases family_descends (prefixWord ++ tailWord_88210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88225 : List Nat := [1, 2, 3, 3, 1, 2, 2, 1, 3, 4]
def baseStart_88225 : Nat := 118140960795 + 88225 * 2 ^ 59
def prefixEnd_88225 : Nat := 4983230072969 + 3 ^ 40 * 88225 * 2
def baseEnd_88225 : Nat := 30201220495348368654511

theorem tailTrace_88225 : CollatzResearch.WordTrace tailWord_88225 prefixEnd_88225 30201220495348368654511 := by
  unfold tailWord_88225
  simp only [CollatzResearch.WordTrace]
  refine ⟨3217830105383367475514129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2145220070255578317009419 3217830105383367475514129)
  ·
    refine ⟨2413372579037525606635597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3217830105383367475514129 2413372579037525606635597)
    ·
      refine ⟨905014717139072102488349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2413372579037525606635597 905014717139072102488349)
      ·
        refine ⟨339380518927152038433131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 905014717139072102488349 339380518927152038433131)
        ·
          refine ⟨509070778390728057649697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339380518927152038433131 509070778390728057649697)
          ·
            refine ⟨381803083793046043237273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 509070778390728057649697 381803083793046043237273)
            ·
              refine ⟨286352312844784532427955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 381803083793046043237273 286352312844784532427955)
              ·
                refine ⟨429528469267176798641933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 286352312844784532427955 429528469267176798641933)
                ·
                  refine ⟨161073175975191299490725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 429528469267176798641933 161073175975191299490725)
                  ·
                    refine ⟨30201220495348368654511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 161073175975191299490725 30201220495348368654511)
                    ·
                      rfl

theorem cell22_88225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_88225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_88225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_88225 prefixEnd_88225 := by exact prefixLift 88225
  have htrace : WordTrace (prefixWord ++ tailWord_88225) baseStart_88225 baseEnd_88225 := by
    simpa [prefixWord, tailWord_88225, baseEnd_88225] using wordTrace_append hprefix tailTrace_88225
  have hstable : (prefixWord ++ tailWord_88225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88225).length < 2 ^ (prefixWord ++ tailWord_88225).sum := by decide
  have hdescent : baseEnd_88225 < baseStart_88225 := by decide
  rcases family_descends (prefixWord ++ tailWord_88225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88270 : List Nat := [4, 1, 1, 1, 4, 1, 1, 2, 1, 6]
def baseStart_88270 : Nat := 118140960795 + 88270 * 2 ^ 59
def prefixEnd_88270 : Nat := 4983230072969 + 3 ^ 40 * 88270 * 2
def baseEnd_88270 : Nat := 30216624914983251279373

theorem tailTrace_88270 : CollatzResearch.WordTrace tailWord_88270 prefixEnd_88270 30216624914983251279373 := by
  unfold tailWord_88270
  simp only [CollatzResearch.WordTrace]
  refine ⟨402433923777542520112783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2146314260146893440601509 402433923777542520112783)
  ·
    refine ⟨603650885666313780169175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 402433923777542520112783 603650885666313780169175)
    ·
      refine ⟨905476328499470670253763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 603650885666313780169175 905476328499470670253763)
      ·
        refine ⟨1358214492749206005380645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 905476328499470670253763 1358214492749206005380645)
        ·
          refine ⟨254665217390476126008871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1358214492749206005380645 254665217390476126008871)
          ·
            refine ⟨381997826085714189013307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254665217390476126008871 381997826085714189013307)
            ·
              refine ⟨572996739128571283519961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 381997826085714189013307 572996739128571283519961)
              ·
                refine ⟨429747554346428462639971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 572996739128571283519961 429747554346428462639971)
                ·
                  refine ⟨644621331519642693959957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 429747554346428462639971 644621331519642693959957)
                  ·
                    refine ⟨30216624914983251279373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 644621331519642693959957 30216624914983251279373)
                    ·
                      rfl

theorem cell22_88270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_88270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_88270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_88270 prefixEnd_88270 := by exact prefixLift 88270
  have htrace : WordTrace (prefixWord ++ tailWord_88270) baseStart_88270 baseEnd_88270 := by
    simpa [prefixWord, tailWord_88270, baseEnd_88270] using wordTrace_append hprefix tailTrace_88270
  have hstable : (prefixWord ++ tailWord_88270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88270).length < 2 ^ (prefixWord ++ tailWord_88270).sum := by decide
  have hdescent : baseEnd_88270 < baseStart_88270 := by decide
  rcases family_descends (prefixWord ++ tailWord_88270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88291 : List Nat := [1, 1, 1, 8, 1, 2, 1, 3, 4]
def baseStart_88291 : Nat := 118140960795 + 88291 * 2 ^ 59
def prefixEnd_88291 : Nat := 4983230072969 + 3 ^ 40 * 88291 * 2
def baseEnd_88291 : Nat := 10074604548048732168103

theorem tailTrace_88291 : CollatzResearch.WordTrace tailWord_88291 prefixEnd_88291 10074604548048732168103 := by
  unfold tailWord_88291
  simp only [CollatzResearch.WordTrace]
  refine ⟨3220237323144260747416727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2146824882096173831611151 3220237323144260747416727)
  ·
    refine ⟨4830355984716391121125091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3220237323144260747416727 4830355984716391121125091)
    ·
      refine ⟨7245533977074586681687637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4830355984716391121125091 7245533977074586681687637)
      ·
        refine ⟨84908601293842812676027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 7245533977074586681687637 84908601293842812676027)
        ·
          refine ⟨127362901940764219014041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84908601293842812676027 127362901940764219014041)
          ·
            refine ⟨95522176455573164260531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127362901940764219014041 95522176455573164260531)
            ·
              refine ⟨143283264683359746390797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95522176455573164260531 143283264683359746390797)
              ·
                refine ⟨53731224256259904896549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 143283264683359746390797 53731224256259904896549)
                ·
                  refine ⟨10074604548048732168103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53731224256259904896549 10074604548048732168103)
                  ·
                    rfl

theorem cell22_88291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 3, 4].length) (baseStart_88291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_88291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_88291 prefixEnd_88291 := by exact prefixLift 88291
  have htrace : WordTrace (prefixWord ++ tailWord_88291) baseStart_88291 baseEnd_88291 := by
    simpa [prefixWord, tailWord_88291, baseEnd_88291] using wordTrace_append hprefix tailTrace_88291
  have hstable : (prefixWord ++ tailWord_88291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88291).length < 2 ^ (prefixWord ++ tailWord_88291).sum := by decide
  have hdescent : baseEnd_88291 < baseStart_88291 := by decide
  rcases family_descends (prefixWord ++ tailWord_88291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88377 : List Nat := [1, 2, 1, 6, 1, 1, 1, 2, 3, 4]
def baseStart_88377 : Nat := 118140960795 + 88377 * 2 ^ 59
def prefixEnd_88377 : Nat := 4983230072969 + 3 ^ 40 * 88377 * 2
def baseEnd_88377 : Nat := 30253253201670638854045

theorem tailTrace_88377 : CollatzResearch.WordTrace tailWord_88377 prefixEnd_88377 30253253201670638854045 := by
  unfold tailWord_88377
  simp only [CollatzResearch.WordTrace]
  refine ⟨3223374000832697435047385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2148916000555131623364923 3223374000832697435047385)
  ·
    refine ⟨2417530500624523076285539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3223374000832697435047385 2417530500624523076285539)
    ·
      refine ⟨3626295750936784614428309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2417530500624523076285539 3626295750936784614428309)
      ·
        refine ⟨169982613325161778801327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3626295750936784614428309 169982613325161778801327)
        ·
          refine ⟨254973919987742668201991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169982613325161778801327 254973919987742668201991)
          ·
            refine ⟨382460879981614002302987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254973919987742668201991 382460879981614002302987)
            ·
              refine ⟨573691319972421003454481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 382460879981614002302987 573691319972421003454481)
              ·
                refine ⟨430268489979315752590861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 573691319972421003454481 430268489979315752590861)
                ·
                  refine ⟨161350683742243407221573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 430268489979315752590861 161350683742243407221573)
                  ·
                    refine ⟨30253253201670638854045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 161350683742243407221573 30253253201670638854045)
                    ·
                      rfl

theorem cell22_88377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 4].length) (baseStart_88377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_88377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_88377 prefixEnd_88377 := by exact prefixLift 88377
  have htrace : WordTrace (prefixWord ++ tailWord_88377) baseStart_88377 baseEnd_88377 := by
    simpa [prefixWord, tailWord_88377, baseEnd_88377] using wordTrace_append hprefix tailTrace_88377
  have hstable : (prefixWord ++ tailWord_88377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88377).length < 2 ^ (prefixWord ++ tailWord_88377).sum := by decide
  have hdescent : baseEnd_88377 < baseStart_88377 := by decide
  rcases family_descends (prefixWord ++ tailWord_88377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88407 : List Nat := [1, 1, 3, 2, 3, 1, 2, 2, 4, 3]
def baseStart_88407 : Nat := 118140960795 + 88407 * 2 ^ 59
def prefixEnd_88407 : Nat := 4983230072969 + 3 ^ 40 * 88407 * 2
def baseEnd_88407 : Nat := 30263522814760560603953

theorem tailTrace_88407 : CollatzResearch.WordTrace tailWord_88407 prefixEnd_88407 30263522814760560603953 := by
  unfold tailWord_88407
  simp only [CollatzResearch.WordTrace]
  refine ⟨3224468190724012558639475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2149645460482675039092983 3224468190724012558639475)
  ·
    refine ⟨4836702286086018837959213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3224468190724012558639475 4836702286086018837959213)
    ·
      refine ⟨1813763357282257064234705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4836702286086018837959213 1813763357282257064234705)
      ·
        refine ⟨1360322517961692798176029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1813763357282257064234705 1360322517961692798176029)
        ·
          refine ⟨510120944235634799316011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1360322517961692798176029 510120944235634799316011)
          ·
            refine ⟨765181416353452198974017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510120944235634799316011 765181416353452198974017)
            ·
              refine ⟨573886062265089149230513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 765181416353452198974017 573886062265089149230513)
              ·
                refine ⟨430414546698816861922885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 573886062265089149230513 430414546698816861922885)
                ·
                  refine ⟨80702727506028161610541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 430414546698816861922885 80702727506028161610541)
                  ·
                    refine ⟨30263522814760560603953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 80702727506028161610541 30263522814760560603953)
                    ·
                      rfl

theorem cell22_88407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 2, 4, 3].length) (baseStart_88407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_88407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_88407 prefixEnd_88407 := by exact prefixLift 88407
  have htrace : WordTrace (prefixWord ++ tailWord_88407) baseStart_88407 baseEnd_88407 := by
    simpa [prefixWord, tailWord_88407, baseEnd_88407] using wordTrace_append hprefix tailTrace_88407
  have hstable : (prefixWord ++ tailWord_88407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88407).length < 2 ^ (prefixWord ++ tailWord_88407).sum := by decide
  have hdescent : baseEnd_88407 < baseStart_88407 := by decide
  rcases family_descends (prefixWord ++ tailWord_88407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88420 : List Nat := [2, 3, 1, 1, 3, 1, 11]
def baseStart_88420 : Nat := 118140960795 + 88420 * 2 ^ 59
def prefixEnd_88420 : Nat := 4983230072969 + 3 ^ 40 * 88420 * 2
def baseEnd_88420 : Nat := 1121036036312328149219

theorem tailTrace_88420 : CollatzResearch.WordTrace tailWord_88420 prefixEnd_88420 1121036036312328149219 := by
  unfold tailWord_88420
  simp only [CollatzResearch.WordTrace]
  refine ⟨1612471169838457889431357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2149961559784610519241809 1612471169838457889431357)
  ·
    refine ⟨604676688689421708536759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1612471169838457889431357 604676688689421708536759)
    ·
      refine ⟨907015033034132562805139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 604676688689421708536759 907015033034132562805139)
      ·
        refine ⟨1360522549551198844207709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 907015033034132562805139 1360522549551198844207709)
        ·
          refine ⟨510195956081699566577891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1360522549551198844207709 510195956081699566577891)
          ·
            refine ⟨765293934122549349866837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510195956081699566577891 765293934122549349866837)
            ·
              refine ⟨1121036036312328149219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 765293934122549349866837 1121036036312328149219)
              ·
                rfl

theorem cell22_88420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 11].length) (baseStart_88420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_88420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_88420 prefixEnd_88420 := by exact prefixLift 88420
  have htrace : WordTrace (prefixWord ++ tailWord_88420) baseStart_88420 baseEnd_88420 := by
    simpa [prefixWord, tailWord_88420, baseEnd_88420] using wordTrace_append hprefix tailTrace_88420
  have hstable : (prefixWord ++ tailWord_88420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88420).length < 2 ^ (prefixWord ++ tailWord_88420).sum := by decide
  have hdescent : baseEnd_88420 < baseStart_88420 := by decide
  rcases family_descends (prefixWord ++ tailWord_88420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88424 : List Nat := [2, 1, 4, 2, 2, 2, 1, 1, 4, 3]
def baseStart_88424 : Nat := 118140960795 + 88424 * 2 ^ 59
def prefixEnd_88424 : Nat := 4983230072969 + 3 ^ 40 * 88424 * 2
def baseEnd_88424 : Nat := 30269342262178182928901

theorem tailTrace_88424 : CollatzResearch.WordTrace tailWord_88424 prefixEnd_88424 30269342262178182928901 := by
  unfold tailWord_88424
  simp only [CollatzResearch.WordTrace]
  refine ⟨1612544115831212231004163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2150058821108282974672217 1612544115831212231004163)
  ·
    refine ⟨2418816173746818346506245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1612544115831212231004163 2418816173746818346506245)
    ·
      refine ⟨453528032577528439969921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2418816173746818346506245 453528032577528439969921)
      ·
        refine ⟨340146024433146329977441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 453528032577528439969921 340146024433146329977441)
        ·
          refine ⟨255109518324859747483081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 340146024433146329977441 255109518324859747483081)
          ·
            refine ⟨191332138743644810612311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255109518324859747483081 191332138743644810612311)
            ·
              refine ⟨286998208115467215918467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191332138743644810612311 286998208115467215918467)
              ·
                refine ⟨430497312173200823877701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 286998208115467215918467 430497312173200823877701)
                ·
                  refine ⟨80718246032475154477069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 430497312173200823877701 80718246032475154477069)
                  ·
                    refine ⟨30269342262178182928901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 80718246032475154477069 30269342262178182928901)
                    ·
                      rfl

theorem cell22_88424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_88424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_88424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_88424 prefixEnd_88424 := by exact prefixLift 88424
  have htrace : WordTrace (prefixWord ++ tailWord_88424) baseStart_88424 baseEnd_88424 := by
    simpa [prefixWord, tailWord_88424, baseEnd_88424] using wordTrace_append hprefix tailTrace_88424
  have hstable : (prefixWord ++ tailWord_88424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88424).length < 2 ^ (prefixWord ++ tailWord_88424).sum := by decide
  have hdescent : baseEnd_88424 < baseStart_88424 := by decide
  rcases family_descends (prefixWord ++ tailWord_88424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88482 : List Nat := [3, 3, 1, 2, 1, 1, 1, 3, 7]
def baseStart_88482 : Nat := 118140960795 + 88482 * 2 ^ 59
def prefixEnd_88482 : Nat := 4983230072969 + 3 ^ 40 * 88482 * 2
def baseEnd_88482 : Nat := 10096398949161788326241

theorem tailTrace_88482 : CollatzResearch.WordTrace tailWord_88482 prefixEnd_88482 10096398949161788326241 := by
  unfold tailWord_88482
  simp only [CollatzResearch.WordTrace]
  refine ⟨806800916363075091904925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2151469110301533578413133 806800916363075091904925)
  ·
    refine ⟨302550343636153159464347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 806800916363075091904925 302550343636153159464347)
    ·
      refine ⟨453825515454229739196521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302550343636153159464347 453825515454229739196521)
      ·
        refine ⟨340369136590672304397391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 453825515454229739196521 340369136590672304397391)
        ·
          refine ⟨510553704886008456596087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340369136590672304397391 510553704886008456596087)
          ·
            refine ⟨765830557329012684894131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510553704886008456596087 765830557329012684894131)
            ·
              refine ⟨1148745835993519027341197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 765830557329012684894131 1148745835993519027341197)
              ·
                refine ⟨430779688497569635252949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1148745835993519027341197 430779688497569635252949)
                ·
                  refine ⟨10096398949161788326241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 430779688497569635252949 10096398949161788326241)
                  ·
                    rfl

theorem cell22_88482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_88482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_88482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_88482 prefixEnd_88482 := by exact prefixLift 88482
  have htrace : WordTrace (prefixWord ++ tailWord_88482) baseStart_88482 baseEnd_88482 := by
    simpa [prefixWord, tailWord_88482, baseEnd_88482] using wordTrace_append hprefix tailTrace_88482
  have hstable : (prefixWord ++ tailWord_88482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88482).length < 2 ^ (prefixWord ++ tailWord_88482).sum := by decide
  have hdescent : baseEnd_88482 < baseStart_88482 := by decide
  rcases family_descends (prefixWord ++ tailWord_88482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88495 : List Nat := [1, 1, 2, 1, 2, 2, 1, 1, 1, 10]
def baseStart_88495 : Nat := 118140960795 + 88495 * 2 ^ 59
def prefixEnd_88495 : Nat := 4983230072969 + 3 ^ 40 * 88495 * 2
def baseEnd_88495 : Nat := 30293647013157664403683

theorem tailTrace_88495 : CollatzResearch.WordTrace tailWord_88495 prefixEnd_88495 30293647013157664403683 := by
  unfold tailWord_88495
  simp only [CollatzResearch.WordTrace]
  refine ⟨3227677814405203587842939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2151785209603469058561959 3227677814405203587842939)
  ·
    refine ⟨4841516721607805381764409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3227677814405203587842939 4841516721607805381764409)
    ·
      refine ⟨3631137541205854036323307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4841516721607805381764409 3631137541205854036323307)
      ·
        refine ⟨5446706311808781054484961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3631137541205854036323307 5446706311808781054484961)
        ·
          refine ⟨4085029733856585790863721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5446706311808781054484961 4085029733856585790863721)
          ·
            refine ⟨3063772300392439343147791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4085029733856585790863721 3063772300392439343147791)
            ·
              refine ⟨4595658450588659014721687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3063772300392439343147791 4595658450588659014721687)
              ·
                refine ⟨6893487675882988522082531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4595658450588659014721687 6893487675882988522082531)
                ·
                  refine ⟨10340231513824482783123797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6893487675882988522082531 10340231513824482783123797)
                  ·
                    refine ⟨30293647013157664403683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 10340231513824482783123797 30293647013157664403683)
                    ·
                      rfl

theorem cell22_88495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 10].length) (baseStart_88495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_88495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_88495 prefixEnd_88495 := by exact prefixLift 88495
  have htrace : WordTrace (prefixWord ++ tailWord_88495) baseStart_88495 baseEnd_88495 := by
    simpa [prefixWord, tailWord_88495, baseEnd_88495] using wordTrace_append hprefix tailTrace_88495
  have hstable : (prefixWord ++ tailWord_88495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88495).length < 2 ^ (prefixWord ++ tailWord_88495).sum := by decide
  have hdescent : baseEnd_88495 < baseStart_88495 := by decide
  rcases family_descends (prefixWord ++ tailWord_88495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88544 : List Nat := [2, 1, 1, 3, 1, 1, 5, 4, 4]
def baseStart_88544 : Nat := 118140960795 + 88544 * 2 ^ 59
def prefixEnd_88544 : Nat := 4983230072969 + 3 ^ 40 * 88544 * 2
def baseEnd_88544 : Nat := 10103473571512623309511

theorem tailTrace_88544 : CollatzResearch.WordTrace tailWord_88544 prefixEnd_88544 10103473571512623309511 := by
  unfold tailWord_88544
  simp only [CollatzResearch.WordTrace]
  refine ⟨1614732495613842478188343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2152976660818456637584457 1614732495613842478188343)
  ·
    refine ⟨2422098743420763717282515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1614732495613842478188343 2422098743420763717282515)
    ·
      refine ⟨3633148115131145575923773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2422098743420763717282515 3633148115131145575923773)
      ·
        refine ⟨1362430543174179590971415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3633148115131145575923773 1362430543174179590971415)
        ·
          refine ⟨2043645814761269386457123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1362430543174179590971415 2043645814761269386457123)
          ·
            refine ⟨3065468722141904079685685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2043645814761269386457123 3065468722141904079685685)
            ·
              refine ⟨287387692700803507470533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3065468722141904079685685 287387692700803507470533)
              ·
                refine ⟨53885192381400657650725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 287387692700803507470533 53885192381400657650725)
                ·
                  refine ⟨10103473571512623309511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53885192381400657650725 10103473571512623309511)
                  ·
                    rfl

theorem cell22_88544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 4, 4].length) (baseStart_88544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_88544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_88544 prefixEnd_88544 := by exact prefixLift 88544
  have htrace : WordTrace (prefixWord ++ tailWord_88544) baseStart_88544 baseEnd_88544 := by
    simpa [prefixWord, tailWord_88544, baseEnd_88544] using wordTrace_append hprefix tailTrace_88544
  have hstable : (prefixWord ++ tailWord_88544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88544).length < 2 ^ (prefixWord ++ tailWord_88544).sum := by decide
  have hdescent : baseEnd_88544 < baseStart_88544 := by decide
  rcases family_descends (prefixWord ++ tailWord_88544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88602 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 1, 8]
def baseStart_88602 : Nat := 118140960795 + 88602 * 2 ^ 59
def prefixEnd_88602 : Nat := 4983230072969 + 3 ^ 40 * 88602 * 2
def baseEnd_88602 : Nat := 30330275299845051978355

theorem tailTrace_88602 : CollatzResearch.WordTrace tailWord_88602 prefixEnd_88602 30330275299845051978355 := by
  unfold tailWord_88602
  simp only [CollatzResearch.WordTrace]
  refine ⟨807895106254390215497015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2154386950011707241325373 807895106254390215497015)
  ·
    refine ⟨1211842659381585323245523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 807895106254390215497015 1211842659381585323245523)
    ·
      refine ⟨1817763989072377984868285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1211842659381585323245523 1817763989072377984868285)
      ·
        refine ⟨681661495902141744325607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1817763989072377984868285 681661495902141744325607)
        ·
          refine ⟨1022492243853212616488411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 681661495902141744325607 1022492243853212616488411)
          ·
            refine ⟨1533738365779818924732617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1022492243853212616488411 1533738365779818924732617)
            ·
              refine ⟨1150303774334864193549463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1533738365779818924732617 1150303774334864193549463)
              ·
                refine ⟨1725455661502296290324195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1150303774334864193549463 1725455661502296290324195)
                ·
                  refine ⟨2588183492253444435486293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1725455661502296290324195 2588183492253444435486293)
                  ·
                    refine ⟨30330275299845051978355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2588183492253444435486293 30330275299845051978355)
                    ·
                      rfl

theorem cell22_88602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_88602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_88602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_88602 prefixEnd_88602 := by exact prefixLift 88602
  have htrace : WordTrace (prefixWord ++ tailWord_88602) baseStart_88602 baseEnd_88602 := by
    simpa [prefixWord, tailWord_88602, baseEnd_88602] using wordTrace_append hprefix tailTrace_88602
  have hstable : (prefixWord ++ tailWord_88602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88602).length < 2 ^ (prefixWord ++ tailWord_88602).sum := by decide
  have hdescent : baseEnd_88602 < baseStart_88602 := by decide
  rcases family_descends (prefixWord ++ tailWord_88602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88743 : List Nat := [1, 1, 6, 3, 1, 1, 1, 1, 1, 6]
def baseStart_88743 : Nat := 118140960795 + 88743 * 2 ^ 59
def prefixEnd_88743 : Nat := 4983230072969 + 3 ^ 40 * 88743 * 2
def baseEnd_88743 : Nat := 30378542481367684202923

theorem tailTrace_88743 : CollatzResearch.WordTrace tailWord_88743 prefixEnd_88743 30378542481367684202923 := by
  unfold tailWord_88743
  simp only [CollatzResearch.WordTrace]
  refine ⟨3236723117506741942870883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2157815411671161295247255 3236723117506741942870883)
  ·
    refine ⟨4855084676260112914306325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3236723117506741942870883 4855084676260112914306325)
    ·
      refine ⟨227582094199692792858109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4855084676260112914306325 227582094199692792858109)
      ·
        refine ⟨85343285324884797321791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227582094199692792858109 85343285324884797321791)
        ·
          refine ⟨128014927987327195982687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85343285324884797321791 128014927987327195982687)
          ·
            refine ⟨192022391980990793974031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128014927987327195982687 192022391980990793974031)
            ·
              refine ⟨288033587971486190961047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192022391980990793974031 288033587971486190961047)
              ·
                refine ⟨432050381957229286441571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 288033587971486190961047 432050381957229286441571)
                ·
                  refine ⟨648075572935843929662357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 432050381957229286441571 648075572935843929662357)
                  ·
                    refine ⟨30378542481367684202923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 648075572935843929662357 30378542481367684202923)
                    ·
                      rfl

theorem cell22_88743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_88743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_88743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_88743 prefixEnd_88743 := by exact prefixLift 88743
  have htrace : WordTrace (prefixWord ++ tailWord_88743) baseStart_88743 baseEnd_88743 := by
    simpa [prefixWord, tailWord_88743, baseEnd_88743] using wordTrace_append hprefix tailTrace_88743
  have hstable : (prefixWord ++ tailWord_88743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88743).length < 2 ^ (prefixWord ++ tailWord_88743).sum := by decide
  have hdescent : baseEnd_88743 < baseStart_88743 := by decide
  rcases family_descends (prefixWord ++ tailWord_88743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88758 : List Nat := [5, 1, 3, 1, 2, 1, 9]
def baseStart_88758 : Nat := 118140960795 + 88758 * 2 ^ 59
def prefixEnd_88758 : Nat := 4983230072969 + 3 ^ 40 * 88758 * 2
def baseEnd_88758 : Nat := 1125321381033801669551

theorem tailTrace_88758 : CollatzResearch.WordTrace tailWord_88758 prefixEnd_88758 1125321381033801669551 := by
  unfold tailWord_88758
  simp only [CollatzResearch.WordTrace]
  refine ⟨202329388278274969041683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2158180141634933003111285 202329388278274969041683)
  ·
    refine ⟨303494082417412453562525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 202329388278274969041683 303494082417412453562525)
    ·
      refine ⟨113810280906529670085947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 303494082417412453562525 113810280906529670085947)
      ·
        refine ⟨170715421359794505128921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113810280906529670085947 170715421359794505128921)
        ·
          refine ⟨128036566019845878846691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170715421359794505128921 128036566019845878846691)
          ·
            refine ⟨192054849029768818270037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128036566019845878846691 192054849029768818270037)
            ·
              refine ⟨1125321381033801669551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 192054849029768818270037 1125321381033801669551)
              ·
                rfl

theorem cell22_88758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 9].length) (baseStart_88758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_88758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_88758 prefixEnd_88758 := by exact prefixLift 88758
  have htrace : WordTrace (prefixWord ++ tailWord_88758) baseStart_88758 baseEnd_88758 := by
    simpa [prefixWord, tailWord_88758, baseEnd_88758] using wordTrace_append hprefix tailTrace_88758
  have hstable : (prefixWord ++ tailWord_88758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88758).length < 2 ^ (prefixWord ++ tailWord_88758).sum := by decide
  have hdescent : baseEnd_88758 < baseStart_88758 := by decide
  rcases family_descends (prefixWord ++ tailWord_88758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88816 : List Nat := [2, 1, 1, 1, 3, 1, 3, 5, 1, 4]
def baseStart_88816 : Nat := 118140960795 + 88816 * 2 ^ 59
def prefixEnd_88816 : Nat := 4983230072969 + 3 ^ 40 * 88816 * 2
def baseEnd_88816 : Nat := 30403531873219827127699

theorem tailTrace_88816 : CollatzResearch.WordTrace tailWord_88816 prefixEnd_88816 30403531873219827127699 := by
  unfold tailWord_88816
  simp only [CollatzResearch.WordTrace]
  refine ⟨1619692823121137705139151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2159590430828183606852201 1619692823121137705139151)
  ·
    refine ⟨2429539234681706557708727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1619692823121137705139151 2429539234681706557708727)
    ·
      refine ⟨3644308852022559836563091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2429539234681706557708727 3644308852022559836563091)
      ·
        refine ⟨5466463278033839754844637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3644308852022559836563091 5466463278033839754844637)
        ·
          refine ⟨2049923729262689908066739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5466463278033839754844637 2049923729262689908066739)
          ·
            refine ⟨3074885593894034862100109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2049923729262689908066739 3074885593894034862100109)
            ·
              refine ⟨1153082097710263073287541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3074885593894034862100109 1153082097710263073287541)
              ·
                refine ⟨108101446660337163120707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1153082097710263073287541 108101446660337163120707)
                ·
                  refine ⟨162152169990505744681061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108101446660337163120707 162152169990505744681061)
                  ·
                    refine ⟨30403531873219827127699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 162152169990505744681061 30403531873219827127699)
                    ·
                      rfl

theorem cell22_88816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 1, 4].length) (baseStart_88816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_88816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_88816 prefixEnd_88816 := by exact prefixLift 88816
  have htrace : WordTrace (prefixWord ++ tailWord_88816) baseStart_88816 baseEnd_88816 := by
    simpa [prefixWord, tailWord_88816, baseEnd_88816] using wordTrace_append hprefix tailTrace_88816
  have hstable : (prefixWord ++ tailWord_88816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88816).length < 2 ^ (prefixWord ++ tailWord_88816).sum := by decide
  have hdescent : baseEnd_88816 < baseStart_88816 := by decide
  rcases family_descends (prefixWord ++ tailWord_88816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88846 : List Nat := [4, 1, 1, 2, 1, 1, 1, 5, 1, 5]
def baseStart_88846 : Nat := 118140960795 + 88846 * 2 ^ 59
def prefixEnd_88846 : Nat := 4983230072969 + 3 ^ 40 * 88846 * 2
def baseEnd_88846 : Nat := 30413801486309748877607

theorem tailTrace_88846 : CollatzResearch.WordTrace tailWord_88846 prefixEnd_88846 30413801486309748877607 := by
  unfold tailWord_88846
  simp only [CollatzResearch.WordTrace]
  refine ⟨405059979516698816733799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2160319890755727022580261 405059979516698816733799)
  ·
    refine ⟨607589969275048225100699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 405059979516698816733799 607589969275048225100699)
    ·
      refine ⟨911384953912572337651049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 607589969275048225100699 911384953912572337651049)
      ·
        refine ⟨683538715434429253238287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 911384953912572337651049 683538715434429253238287)
        ·
          refine ⟨1025308073151643879857431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 683538715434429253238287 1025308073151643879857431)
          ·
            refine ⟨1537962109727465819786147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1025308073151643879857431 1537962109727465819786147)
            ·
              refine ⟨2306943164591198729679221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1537962109727465819786147 2306943164591198729679221)
              ·
                refine ⟨216275921680424880907427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2306943164591198729679221 216275921680424880907427)
                ·
                  refine ⟨324413882520637321361141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 216275921680424880907427 324413882520637321361141)
                  ·
                    refine ⟨30413801486309748877607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 324413882520637321361141 30413801486309748877607)
                    ·
                      rfl

theorem cell22_88846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_88846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_88846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_88846 prefixEnd_88846 := by exact prefixLift 88846
  have htrace : WordTrace (prefixWord ++ tailWord_88846) baseStart_88846 baseEnd_88846 := by
    simpa [prefixWord, tailWord_88846, baseEnd_88846] using wordTrace_append hprefix tailTrace_88846
  have hstable : (prefixWord ++ tailWord_88846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88846).length < 2 ^ (prefixWord ++ tailWord_88846).sum := by decide
  have hdescent : baseEnd_88846 < baseStart_88846 := by decide
  rcases family_descends (prefixWord ++ tailWord_88846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88850 : List Nat := [3, 2, 4, 1, 2, 1, 1, 1, 3, 4]
def baseStart_88850 : Nat := 118140960795 + 88850 * 2 ^ 59
def prefixEnd_88850 : Nat := 4983230072969 + 3 ^ 40 * 88850 * 2
def baseEnd_88850 : Nat := 30415170768055071777595

theorem tailTrace_88850 : CollatzResearch.WordTrace tailWord_88850 prefixEnd_88850 30415170768055071777595 := by
  unfold tailWord_88850
  simp only [CollatzResearch.WordTrace]
  refine ⟨810156432029774804254001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2160417152079399478010669 810156432029774804254001)
  ·
    refine ⟨607617324022331103190501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 810156432029774804254001 607617324022331103190501)
    ·
      refine ⟨113928248254187081848219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 607617324022331103190501 113928248254187081848219)
      ·
        refine ⟨170892372381280622772329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113928248254187081848219 170892372381280622772329)
        ·
          refine ⟨128169279285960467079247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170892372381280622772329 128169279285960467079247)
          ·
            refine ⟨192253918928940700618871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128169279285960467079247 192253918928940700618871)
            ·
              refine ⟨288380878393411050928307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192253918928940700618871 288380878393411050928307)
              ·
                refine ⟨432571317590116576392461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 288380878393411050928307 432571317590116576392461)
                ·
                  refine ⟨162214244096293716147173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 432571317590116576392461 162214244096293716147173)
                  ·
                    refine ⟨30415170768055071777595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 162214244096293716147173 30415170768055071777595)
                    ·
                      rfl

theorem cell22_88850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_88850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_88850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_88850 prefixEnd_88850 := by exact prefixLift 88850
  have htrace : WordTrace (prefixWord ++ tailWord_88850) baseStart_88850 baseEnd_88850 := by
    simpa [prefixWord, tailWord_88850, baseEnd_88850] using wordTrace_append hprefix tailTrace_88850
  have hstable : (prefixWord ++ tailWord_88850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88850).length < 2 ^ (prefixWord ++ tailWord_88850).sum := by decide
  have hdescent : baseEnd_88850 < baseStart_88850 := by decide
  rcases family_descends (prefixWord ++ tailWord_88850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88908 : List Nat := [2, 2, 1, 3, 3, 1, 1, 1, 5, 3]
def baseStart_88908 : Nat := 118140960795 + 88908 * 2 ^ 59
def prefixEnd_88908 : Nat := 4983230072969 + 3 ^ 40 * 88908 * 2
def baseEnd_88908 : Nat := 30435025353362253827417

theorem tailTrace_88908 : CollatzResearch.WordTrace tailWord_88908 prefixEnd_88908 30435025353362253827417 := by
  unfold tailWord_88908
  simp only [CollatzResearch.WordTrace]
  refine ⟨1621370580954487561313689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2161827441272650081751585 1621370580954487561313689)
  ·
    refine ⟨1216027935715865670985267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1621370580954487561313689 1216027935715865670985267)
    ·
      refine ⟨1824041903573798506477901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1216027935715865670985267 1824041903573798506477901)
      ·
        refine ⟨684015713840174439929213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1824041903573798506477901 684015713840174439929213)
        ·
          refine ⟨256505892690065414973455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 684015713840174439929213 256505892690065414973455)
          ·
            refine ⟨384758839035098122460183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256505892690065414973455 384758839035098122460183)
            ·
              refine ⟨577138258552647183690275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 384758839035098122460183 577138258552647183690275)
              ·
                refine ⟨865707387828970775535413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 577138258552647183690275 865707387828970775535413)
                ·
                  refine ⟨81160067608966010206445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 865707387828970775535413 81160067608966010206445)
                  ·
                    refine ⟨30435025353362253827417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 81160067608966010206445 30435025353362253827417)
                    ·
                      rfl

theorem cell22_88908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 5, 3].length) (baseStart_88908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_88908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_88908 prefixEnd_88908 := by exact prefixLift 88908
  have htrace : WordTrace (prefixWord ++ tailWord_88908) baseStart_88908 baseEnd_88908 := by
    simpa [prefixWord, tailWord_88908, baseEnd_88908] using wordTrace_append hprefix tailTrace_88908
  have hstable : (prefixWord ++ tailWord_88908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88908).length < 2 ^ (prefixWord ++ tailWord_88908).sum := by decide
  have hdescent : baseEnd_88908 < baseStart_88908 := by decide
  rcases family_descends (prefixWord ++ tailWord_88908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88942 : List Nat := [4, 1, 2, 3, 2, 1, 2, 1, 3, 3]
def baseStart_88942 : Nat := 118140960795 + 88942 * 2 ^ 59
def prefixEnd_88942 : Nat := 4983230072969 + 3 ^ 40 * 88942 * 2
def baseEnd_88942 : Nat := 30446664248197498477313

theorem tailTrace_88942 : CollatzResearch.WordTrace tailWord_88942 prefixEnd_88942 30446664248197498477313 := by
  unfold tailWord_88942
  simp only [CollatzResearch.WordTrace]
  refine ⟨405497655473224866170635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2162654162523865952910053 405497655473224866170635)
  ·
    refine ⟨608246483209837299255953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 405497655473224866170635 608246483209837299255953)
    ·
      refine ⟨456184862407377974441965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 608246483209837299255953 456184862407377974441965)
      ·
        refine ⟨171069323402766740415737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 456184862407377974441965 171069323402766740415737)
        ·
          refine ⟨128301992552075055311803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171069323402766740415737 128301992552075055311803)
          ·
            refine ⟨192452988828112582967705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128301992552075055311803 192452988828112582967705)
            ·
              refine ⟨144339741621084437225779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192452988828112582967705 144339741621084437225779)
              ·
                refine ⟨216509612431626655838669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144339741621084437225779 216509612431626655838669)
                ·
                  refine ⟨81191104661859995939501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 216509612431626655838669 81191104661859995939501)
                  ·
                    refine ⟨30446664248197498477313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 81191104661859995939501 30446664248197498477313)
                    ·
                      rfl

theorem cell22_88942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_88942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_88942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_88942 prefixEnd_88942 := by exact prefixLift 88942
  have htrace : WordTrace (prefixWord ++ tailWord_88942) baseStart_88942 baseEnd_88942 := by
    simpa [prefixWord, tailWord_88942, baseEnd_88942] using wordTrace_append hprefix tailTrace_88942
  have hstable : (prefixWord ++ tailWord_88942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88942).length < 2 ^ (prefixWord ++ tailWord_88942).sum := by decide
  have hdescent : baseEnd_88942 < baseStart_88942 := by decide
  rcases family_descends (prefixWord ++ tailWord_88942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88951 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 5, 4]
def baseStart_88951 : Nat := 118140960795 + 88951 * 2 ^ 59
def prefixEnd_88951 : Nat := 4983230072969 + 3 ^ 40 * 88951 * 2
def baseEnd_88951 : Nat := 30449745132124475002285

theorem tailTrace_88951 : CollatzResearch.WordTrace tailWord_88951 prefixEnd_88951 30449745132124475002285 := by
  unfold tailWord_88951
  simp only [CollatzResearch.WordTrace]
  refine ⟨3244309500753193466442707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2162873000502128977628471 3244309500753193466442707)
  ·
    refine ⟨4866464251129790199664061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3244309500753193466442707 4866464251129790199664061)
    ·
      refine ⟨1824924094173671324874023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4866464251129790199664061 1824924094173671324874023)
      ·
        refine ⟨2737386141260506987311035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1824924094173671324874023 2737386141260506987311035)
        ·
          refine ⟨4106079211890760480966553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2737386141260506987311035 4106079211890760480966553)
          ·
            refine ⟨3079559408918070360724915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4106079211890760480966553 3079559408918070360724915)
            ·
              refine ⟨4619339113377105541087373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3079559408918070360724915 4619339113377105541087373)
              ·
                refine ⟨1732252167516414577907765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4619339113377105541087373 1732252167516414577907765)
                ·
                  refine ⟨162398640704663866678853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1732252167516414577907765 162398640704663866678853)
                  ·
                    refine ⟨30449745132124475002285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 162398640704663866678853 30449745132124475002285)
                    ·
                      rfl

theorem cell22_88951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 4].length) (baseStart_88951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_88951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_88951 prefixEnd_88951 := by exact prefixLift 88951
  have htrace : WordTrace (prefixWord ++ tailWord_88951) baseStart_88951 baseEnd_88951 := by
    simpa [prefixWord, tailWord_88951, baseEnd_88951] using wordTrace_append hprefix tailTrace_88951
  have hstable : (prefixWord ++ tailWord_88951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88951).length < 2 ^ (prefixWord ++ tailWord_88951).sum := by decide
  have hdescent : baseEnd_88951 < baseStart_88951 := by decide
  rcases family_descends (prefixWord ++ tailWord_88951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89013 : List Nat := [1, 3, 3, 2, 1, 1, 1, 2, 4, 4]
def baseStart_89013 : Nat := 118140960795 + 89013 * 2 ^ 59
def prefixEnd_89013 : Nat := 4983230072969 + 3 ^ 40 * 89013 * 2
def baseEnd_89013 : Nat := 30470968999176979952095

theorem tailTrace_89013 : CollatzResearch.WordTrace tailWord_89013 prefixEnd_89013 30470968999176979952095 := by
  unfold tailWord_89013
  simp only [CollatzResearch.WordTrace]
  refine ⟨3246570826528578055199693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2164380551019052036799795 3246570826528578055199693)
  ·
    refine ⟨1217464059948216770699885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3246570826528578055199693 1217464059948216770699885)
    ·
      refine ⟨456549022480581289012457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1217464059948216770699885 456549022480581289012457)
      ·
        refine ⟨342411766860435966759343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 456549022480581289012457 342411766860435966759343)
        ·
          refine ⟨513617650290653950139015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342411766860435966759343 513617650290653950139015)
          ·
            refine ⟨770426475435980925208523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 513617650290653950139015 770426475435980925208523)
            ·
              refine ⟨1155639713153971387812785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 770426475435980925208523 1155639713153971387812785)
              ·
                refine ⟨866729784865478540859589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1155639713153971387812785 866729784865478540859589)
                ·
                  refine ⟨162511834662277226411173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 866729784865478540859589 162511834662277226411173)
                  ·
                    refine ⟨30470968999176979952095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 162511834662277226411173 30470968999176979952095)
                    ·
                      rfl

theorem cell22_89013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_89013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_89013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_89013 prefixEnd_89013 := by exact prefixLift 89013
  have htrace : WordTrace (prefixWord ++ tailWord_89013) baseStart_89013 baseEnd_89013 := by
    simpa [prefixWord, tailWord_89013, baseEnd_89013] using wordTrace_append hprefix tailTrace_89013
  have hstable : (prefixWord ++ tailWord_89013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89013).length < 2 ^ (prefixWord ++ tailWord_89013).sum := by decide
  have hdescent : baseEnd_89013 < baseStart_89013 := by decide
  rcases family_descends (prefixWord ++ tailWord_89013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89178 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 2, 7]
def baseStart_89178 : Nat := 118140960795 + 89178 * 2 ^ 59
def prefixEnd_89178 : Nat := 4983230072969 + 3 ^ 40 * 89178 * 2
def baseEnd_89178 : Nat := 30527451871171549576589

theorem tailTrace_89178 : CollatzResearch.WordTrace tailWord_89178 prefixEnd_89178 30527451871171549576589 := by
  unfold tailWord_89178
  simp only [CollatzResearch.WordTrace]
  refine ⟨813147217732702808739047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2168392580620540823304125 813147217732702808739047)
  ·
    refine ⟨1219720826599054213108571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 813147217732702808739047 1219720826599054213108571)
    ·
      refine ⟨1829581239898581319662857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1219720826599054213108571 1829581239898581319662857)
      ·
        refine ⟨1372185929923935989747143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1829581239898581319662857 1372185929923935989747143)
        ·
          refine ⟨2058278894885903984620715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1372185929923935989747143 2058278894885903984620715)
          ·
            refine ⟨3087418342328855976931073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2058278894885903984620715 3087418342328855976931073)
            ·
              refine ⟨2315563756746641982698305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3087418342328855976931073 2315563756746641982698305)
              ·
                refine ⟨1736672817559981487023729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2315563756746641982698305 1736672817559981487023729)
                ·
                  refine ⟨1302504613169986115267797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1736672817559981487023729 1302504613169986115267797)
                  ·
                    refine ⟨30527451871171549576589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1302504613169986115267797 30527451871171549576589)
                    ·
                      rfl

theorem cell22_89178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_89178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_89178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_89178 prefixEnd_89178 := by exact prefixLift 89178
  have htrace : WordTrace (prefixWord ++ tailWord_89178) baseStart_89178 baseEnd_89178 := by
    simpa [prefixWord, tailWord_89178, baseEnd_89178] using wordTrace_append hprefix tailTrace_89178
  have hstable : (prefixWord ++ tailWord_89178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89178).length < 2 ^ (prefixWord ++ tailWord_89178).sum := by decide
  have hdescent : baseEnd_89178 < baseStart_89178 := by decide
  rcases family_descends (prefixWord ++ tailWord_89178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
