Theory vfmTest0362[no_sig_docs]
Ancestors vfmTestDefs0362
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0362_0.nsv", "result0362_1.nsv", "result0362_2.nsv", "result0362_3.nsv", "result0362_4.nsv"];
val thyn = "vfmTestDefs0362";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
