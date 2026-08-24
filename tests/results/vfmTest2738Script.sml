Theory vfmTest2738[no_sig_docs]
Ancestors vfmTestDefs2738
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2738_0.nsv", "result2738_1.nsv", "result2738_2.nsv", "result2738_3.nsv"];
val thyn = "vfmTestDefs2738";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
