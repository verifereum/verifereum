Theory vfmTest2146[no_sig_docs]
Ancestors vfmTestDefs2146
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2146_0.nsv", "result2146_1.nsv", "result2146_2.nsv", "result2146_3.nsv", "result2146_4.nsv", "result2146_5.nsv", "result2146_6.nsv", "result2146_7.nsv", "result2146_8.nsv", "result2146_9.nsv", "result2146_10.nsv", "result2146_11.nsv", "result2146_12.nsv", "result2146_13.nsv", "result2146_14.nsv", "result2146_15.nsv", "result2146_16.nsv", "result2146_17.nsv", "result2146_18.nsv", "result2146_19.nsv", "result2146_20.nsv", "result2146_21.nsv", "result2146_22.nsv", "result2146_23.nsv", "result2146_24.nsv", "result2146_25.nsv", "result2146_26.nsv", "result2146_27.nsv", "result2146_28.nsv", "result2146_29.nsv", "result2146_30.nsv", "result2146_31.nsv"];
val thyn = "vfmTestDefs2146";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
