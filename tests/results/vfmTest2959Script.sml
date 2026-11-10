Theory vfmTest2959[no_sig_docs]
Ancestors vfmTestDefs2959
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2959_0.nsv", "result2959_1.nsv", "result2959_2.nsv"];
val thyn = "vfmTestDefs2959";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
