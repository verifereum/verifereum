Theory vfmTest2784[no_sig_docs]
Ancestors vfmTestDefs2784
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2784_0.nsv", "result2784_1.nsv", "result2784_2.nsv", "result2784_3.nsv"];
val thyn = "vfmTestDefs2784";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
