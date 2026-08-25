Theory vfmTest2722[no_sig_docs]
Ancestors vfmTestDefs2722
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2722_0.nsv", "result2722_1.nsv", "result2722_2.nsv", "result2722_3.nsv"];
val thyn = "vfmTestDefs2722";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
