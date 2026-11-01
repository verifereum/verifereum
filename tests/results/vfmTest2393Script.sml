Theory vfmTest2393[no_sig_docs]
Ancestors vfmTestDefs2393
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2393_0.nsv", "result2393_1.nsv", "result2393_2.nsv", "result2393_3.nsv", "result2393_4.nsv", "result2393_5.nsv", "result2393_6.nsv", "result2393_7.nsv", "result2393_8.nsv"];
val thyn = "vfmTestDefs2393";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
