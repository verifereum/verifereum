Theory vfmTest0281[no_sig_docs]
Ancestors vfmTestDefs0281
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0281_0.nsv", "result0281_1.nsv", "result0281_2.nsv", "result0281_3.nsv", "result0281_4.nsv", "result0281_5.nsv", "result0281_6.nsv", "result0281_7.nsv", "result0281_8.nsv", "result0281_9.nsv", "result0281_10.nsv", "result0281_11.nsv", "result0281_12.nsv", "result0281_13.nsv", "result0281_14.nsv", "result0281_15.nsv", "result0281_16.nsv", "result0281_17.nsv", "result0281_18.nsv", "result0281_19.nsv", "result0281_20.nsv", "result0281_21.nsv", "result0281_22.nsv", "result0281_23.nsv", "result0281_24.nsv", "result0281_25.nsv", "result0281_26.nsv", "result0281_27.nsv"];
val thyn = "vfmTestDefs0281";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
