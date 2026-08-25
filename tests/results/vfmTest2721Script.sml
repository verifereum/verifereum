Theory vfmTest2721[no_sig_docs]
Ancestors vfmTestDefs2721
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2721_0.nsv", "result2721_1.nsv", "result2721_2.nsv", "result2721_3.nsv"];
val thyn = "vfmTestDefs2721";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
