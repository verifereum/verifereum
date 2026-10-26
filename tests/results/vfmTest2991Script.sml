Theory vfmTest2991[no_sig_docs]
Ancestors vfmTestDefs2991
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2991_0.nsv", "result2991_1.nsv", "result2991_2.nsv", "result2991_3.nsv", "result2991_4.nsv", "result2991_5.nsv"];
val thyn = "vfmTestDefs2991";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
