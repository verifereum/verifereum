Theory vfmTest0366[no_sig_docs]
Ancestors vfmTestDefs0366
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0366_0.nsv", "result0366_1.nsv", "result0366_2.nsv", "result0366_3.nsv", "result0366_4.nsv", "result0366_5.nsv", "result0366_6.nsv", "result0366_7.nsv", "result0366_8.nsv", "result0366_9.nsv", "result0366_10.nsv", "result0366_11.nsv", "result0366_12.nsv", "result0366_13.nsv", "result0366_14.nsv", "result0366_15.nsv"];
val thyn = "vfmTestDefs0366";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
