Theory vfmTest1652[no_sig_docs]
Ancestors vfmTestDefs1652
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1652_0.nsv", "result1652_1.nsv", "result1652_2.nsv", "result1652_3.nsv"];
val thyn = "vfmTestDefs1652";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
