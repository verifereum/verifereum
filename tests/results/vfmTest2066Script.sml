Theory vfmTest2066[no_sig_docs]
Ancestors vfmTestDefs2066
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2066_0.nsv", "result2066_1.nsv", "result2066_2.nsv", "result2066_3.nsv", "result2066_4.nsv", "result2066_5.nsv", "result2066_6.nsv", "result2066_7.nsv"];
val thyn = "vfmTestDefs2066";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
