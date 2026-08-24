Theory vfmTest0234[no_sig_docs]
Ancestors vfmTestDefs0234
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0234_0.nsv", "result0234_1.nsv", "result0234_2.nsv", "result0234_3.nsv", "result0234_4.nsv", "result0234_5.nsv", "result0234_6.nsv", "result0234_7.nsv", "result0234_8.nsv", "result0234_9.nsv", "result0234_10.nsv", "result0234_11.nsv", "result0234_12.nsv", "result0234_13.nsv", "result0234_14.nsv", "result0234_15.nsv", "result0234_16.nsv", "result0234_17.nsv"];
val thyn = "vfmTestDefs0234";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
