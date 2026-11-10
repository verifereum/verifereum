Theory vfmTest0368[no_sig_docs]
Ancestors vfmTestDefs0368
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0368_0.nsv", "result0368_1.nsv", "result0368_2.nsv", "result0368_3.nsv", "result0368_4.nsv", "result0368_5.nsv", "result0368_6.nsv", "result0368_7.nsv", "result0368_8.nsv", "result0368_9.nsv", "result0368_10.nsv", "result0368_11.nsv", "result0368_12.nsv", "result0368_13.nsv", "result0368_14.nsv", "result0368_15.nsv", "result0368_16.nsv", "result0368_17.nsv", "result0368_18.nsv", "result0368_19.nsv", "result0368_20.nsv", "result0368_21.nsv", "result0368_22.nsv", "result0368_23.nsv", "result0368_24.nsv", "result0368_25.nsv", "result0368_26.nsv", "result0368_27.nsv", "result0368_28.nsv", "result0368_29.nsv", "result0368_30.nsv", "result0368_31.nsv", "result0368_32.nsv", "result0368_33.nsv", "result0368_34.nsv", "result0368_35.nsv"];
val thyn = "vfmTestDefs0368";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
