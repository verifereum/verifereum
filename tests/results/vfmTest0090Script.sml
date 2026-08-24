Theory vfmTest0090[no_sig_docs]
Ancestors vfmTestDefs0090
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0090_0.nsv", "result0090_1.nsv", "result0090_2.nsv", "result0090_3.nsv", "result0090_4.nsv", "result0090_5.nsv", "result0090_6.nsv", "result0090_7.nsv", "result0090_8.nsv", "result0090_9.nsv", "result0090_10.nsv", "result0090_11.nsv", "result0090_12.nsv", "result0090_13.nsv", "result0090_14.nsv", "result0090_15.nsv", "result0090_16.nsv", "result0090_17.nsv"];
val thyn = "vfmTestDefs0090";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
