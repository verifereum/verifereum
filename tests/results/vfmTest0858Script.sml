Theory vfmTest0858[no_sig_docs]
Ancestors vfmTestDefs0858
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0858_0.nsv", "result0858_1.nsv", "result0858_2.nsv", "result0858_3.nsv", "result0858_4.nsv", "result0858_5.nsv", "result0858_6.nsv", "result0858_7.nsv", "result0858_8.nsv", "result0858_9.nsv", "result0858_10.nsv", "result0858_11.nsv", "result0858_12.nsv", "result0858_13.nsv", "result0858_14.nsv", "result0858_15.nsv", "result0858_16.nsv", "result0858_17.nsv", "result0858_18.nsv", "result0858_19.nsv", "result0858_20.nsv", "result0858_21.nsv", "result0858_22.nsv", "result0858_23.nsv"];
val thyn = "vfmTestDefs0858";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
