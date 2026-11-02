Theory vfmTest0929[no_sig_docs]
Ancestors vfmTestDefs0929
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0929_0.nsv", "result0929_1.nsv", "result0929_2.nsv", "result0929_3.nsv", "result0929_4.nsv", "result0929_5.nsv", "result0929_6.nsv", "result0929_7.nsv", "result0929_8.nsv", "result0929_9.nsv", "result0929_10.nsv", "result0929_11.nsv", "result0929_12.nsv", "result0929_13.nsv", "result0929_14.nsv", "result0929_15.nsv", "result0929_16.nsv", "result0929_17.nsv", "result0929_18.nsv", "result0929_19.nsv", "result0929_20.nsv", "result0929_21.nsv", "result0929_22.nsv", "result0929_23.nsv"];
val thyn = "vfmTestDefs0929";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
