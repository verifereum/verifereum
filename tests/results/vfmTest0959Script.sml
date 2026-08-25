Theory vfmTest0959[no_sig_docs]
Ancestors vfmTestDefs0959
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0959_0.nsv", "result0959_1.nsv", "result0959_2.nsv", "result0959_3.nsv", "result0959_4.nsv", "result0959_5.nsv", "result0959_6.nsv", "result0959_7.nsv", "result0959_8.nsv", "result0959_9.nsv", "result0959_10.nsv", "result0959_11.nsv", "result0959_12.nsv", "result0959_13.nsv", "result0959_14.nsv", "result0959_15.nsv", "result0959_16.nsv", "result0959_17.nsv", "result0959_18.nsv", "result0959_19.nsv", "result0959_20.nsv", "result0959_21.nsv", "result0959_22.nsv", "result0959_23.nsv", "result0959_24.nsv", "result0959_25.nsv", "result0959_26.nsv", "result0959_27.nsv", "result0959_28.nsv", "result0959_29.nsv", "result0959_30.nsv", "result0959_31.nsv", "result0959_32.nsv", "result0959_33.nsv"];
val thyn = "vfmTestDefs0959";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
