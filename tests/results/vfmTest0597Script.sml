Theory vfmTest0597[no_sig_docs]
Ancestors vfmTestDefs0597
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0597_0.nsv", "result0597_1.nsv", "result0597_2.nsv", "result0597_3.nsv", "result0597_4.nsv", "result0597_5.nsv", "result0597_6.nsv", "result0597_7.nsv", "result0597_8.nsv", "result0597_9.nsv", "result0597_10.nsv", "result0597_11.nsv", "result0597_12.nsv", "result0597_13.nsv", "result0597_14.nsv", "result0597_15.nsv", "result0597_16.nsv", "result0597_17.nsv", "result0597_18.nsv", "result0597_19.nsv", "result0597_20.nsv", "result0597_21.nsv", "result0597_22.nsv", "result0597_23.nsv", "result0597_24.nsv", "result0597_25.nsv", "result0597_26.nsv", "result0597_27.nsv", "result0597_28.nsv", "result0597_29.nsv", "result0597_30.nsv", "result0597_31.nsv", "result0597_32.nsv", "result0597_33.nsv", "result0597_34.nsv", "result0597_35.nsv", "result0597_36.nsv", "result0597_37.nsv"];
val thyn = "vfmTestDefs0597";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
