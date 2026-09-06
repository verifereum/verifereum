Theory vfmTest2307[no_sig_docs]
Ancestors vfmTestDefs2307
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2307_0.nsv", "result2307_1.nsv", "result2307_2.nsv", "result2307_3.nsv"];
val thyn = "vfmTestDefs2307";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
