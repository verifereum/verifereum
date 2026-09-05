Theory vfmTest2267[no_sig_docs]
Ancestors vfmTestDefs2267
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2267_0.nsv", "result2267_1.nsv", "result2267_2.nsv", "result2267_3.nsv", "result2267_4.nsv", "result2267_5.nsv"];
val thyn = "vfmTestDefs2267";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
