Theory vfmTest0235[no_sig_docs]
Ancestors vfmTestDefs0235
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0235_0.nsv", "result0235_1.nsv", "result0235_2.nsv", "result0235_3.nsv", "result0235_4.nsv", "result0235_5.nsv", "result0235_6.nsv", "result0235_7.nsv", "result0235_8.nsv", "result0235_9.nsv", "result0235_10.nsv", "result0235_11.nsv", "result0235_12.nsv", "result0235_13.nsv", "result0235_14.nsv", "result0235_15.nsv", "result0235_16.nsv", "result0235_17.nsv", "result0235_18.nsv", "result0235_19.nsv", "result0235_20.nsv", "result0235_21.nsv", "result0235_22.nsv", "result0235_23.nsv", "result0235_24.nsv", "result0235_25.nsv", "result0235_26.nsv"];
val thyn = "vfmTestDefs0235";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
