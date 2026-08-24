Theory vfmTest0298[no_sig_docs]
Ancestors vfmTestDefs0298
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0298_0.nsv", "result0298_1.nsv", "result0298_2.nsv", "result0298_3.nsv", "result0298_4.nsv", "result0298_5.nsv", "result0298_6.nsv", "result0298_7.nsv", "result0298_8.nsv", "result0298_9.nsv", "result0298_10.nsv", "result0298_11.nsv", "result0298_12.nsv", "result0298_13.nsv", "result0298_14.nsv", "result0298_15.nsv", "result0298_16.nsv", "result0298_17.nsv", "result0298_18.nsv", "result0298_19.nsv", "result0298_20.nsv", "result0298_21.nsv", "result0298_22.nsv", "result0298_23.nsv", "result0298_24.nsv", "result0298_25.nsv", "result0298_26.nsv", "result0298_27.nsv", "result0298_28.nsv"];
val thyn = "vfmTestDefs0298";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
