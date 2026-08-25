Theory vfmTest2772[no_sig_docs]
Ancestors vfmTestDefs2772
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2772_0.nsv", "result2772_1.nsv", "result2772_2.nsv", "result2772_3.nsv"];
val thyn = "vfmTestDefs2772";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
