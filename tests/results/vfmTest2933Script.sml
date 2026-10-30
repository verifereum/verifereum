Theory vfmTest2933[no_sig_docs]
Ancestors vfmTestDefs2933
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2933_0.nsv", "result2933_1.nsv", "result2933_2.nsv", "result2933_3.nsv", "result2933_4.nsv", "result2933_5.nsv"];
val thyn = "vfmTestDefs2933";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
