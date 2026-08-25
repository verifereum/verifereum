Theory vfmTest1111[no_sig_docs]
Ancestors vfmTestDefs1111
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1111_0.nsv", "result1111_1.nsv", "result1111_2.nsv", "result1111_3.nsv", "result1111_4.nsv", "result1111_5.nsv"];
val thyn = "vfmTestDefs1111";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
