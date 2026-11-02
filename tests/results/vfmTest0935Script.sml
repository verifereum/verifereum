Theory vfmTest0935[no_sig_docs]
Ancestors vfmTestDefs0935
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0935_0.nsv", "result0935_1.nsv", "result0935_2.nsv", "result0935_3.nsv", "result0935_4.nsv", "result0935_5.nsv", "result0935_6.nsv", "result0935_7.nsv", "result0935_8.nsv", "result0935_9.nsv"];
val thyn = "vfmTestDefs0935";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
