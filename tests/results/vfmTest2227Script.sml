Theory vfmTest2227[no_sig_docs]
Ancestors vfmTestDefs2227
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2227_0.nsv", "result2227_1.nsv", "result2227_2.nsv", "result2227_3.nsv", "result2227_4.nsv", "result2227_5.nsv"];
val thyn = "vfmTestDefs2227";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
