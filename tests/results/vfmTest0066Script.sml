Theory vfmTest0066[no_sig_docs]
Ancestors vfmTestDefs0066
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0066_0.nsv", "result0066_1.nsv", "result0066_2.nsv", "result0066_3.nsv", "result0066_4.nsv", "result0066_5.nsv", "result0066_6.nsv", "result0066_7.nsv", "result0066_8.nsv", "result0066_9.nsv"];
val thyn = "vfmTestDefs0066";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
