Theory vfmTest0076[no_sig_docs]
Ancestors vfmTestDefs0076
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0076_0.nsv", "result0076_1.nsv", "result0076_2.nsv", "result0076_3.nsv", "result0076_4.nsv", "result0076_5.nsv", "result0076_6.nsv", "result0076_7.nsv", "result0076_8.nsv", "result0076_9.nsv", "result0076_10.nsv", "result0076_11.nsv", "result0076_12.nsv", "result0076_13.nsv", "result0076_14.nsv", "result0076_15.nsv", "result0076_16.nsv", "result0076_17.nsv"];
val thyn = "vfmTestDefs0076";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
