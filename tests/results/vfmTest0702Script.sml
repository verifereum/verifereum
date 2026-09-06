Theory vfmTest0702[no_sig_docs]
Ancestors vfmTestDefs0702
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0702_0.nsv", "result0702_1.nsv", "result0702_2.nsv", "result0702_3.nsv", "result0702_4.nsv", "result0702_5.nsv", "result0702_6.nsv", "result0702_7.nsv", "result0702_8.nsv", "result0702_9.nsv", "result0702_10.nsv", "result0702_11.nsv", "result0702_12.nsv", "result0702_13.nsv", "result0702_14.nsv", "result0702_15.nsv", "result0702_16.nsv", "result0702_17.nsv", "result0702_18.nsv", "result0702_19.nsv", "result0702_20.nsv", "result0702_21.nsv", "result0702_22.nsv", "result0702_23.nsv"];
val thyn = "vfmTestDefs0702";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
