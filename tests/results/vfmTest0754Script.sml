Theory vfmTest0754[no_sig_docs]
Ancestors vfmTestDefs0754
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0754_0.nsv", "result0754_1.nsv", "result0754_2.nsv", "result0754_3.nsv", "result0754_4.nsv", "result0754_5.nsv", "result0754_6.nsv", "result0754_7.nsv", "result0754_8.nsv", "result0754_9.nsv", "result0754_10.nsv", "result0754_11.nsv", "result0754_12.nsv", "result0754_13.nsv", "result0754_14.nsv", "result0754_15.nsv", "result0754_16.nsv", "result0754_17.nsv", "result0754_18.nsv", "result0754_19.nsv", "result0754_20.nsv", "result0754_21.nsv", "result0754_22.nsv", "result0754_23.nsv", "result0754_24.nsv", "result0754_25.nsv", "result0754_26.nsv", "result0754_27.nsv", "result0754_28.nsv", "result0754_29.nsv", "result0754_30.nsv", "result0754_31.nsv", "result0754_32.nsv", "result0754_33.nsv", "result0754_34.nsv", "result0754_35.nsv"];
val thyn = "vfmTestDefs0754";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
