Theory vfmTest0047[no_sig_docs]
Ancestors vfmTestDefs0047
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0047_0.nsv", "result0047_1.nsv", "result0047_2.nsv", "result0047_3.nsv", "result0047_4.nsv", "result0047_5.nsv", "result0047_6.nsv", "result0047_7.nsv", "result0047_8.nsv", "result0047_9.nsv", "result0047_10.nsv", "result0047_11.nsv", "result0047_12.nsv", "result0047_13.nsv", "result0047_14.nsv", "result0047_15.nsv", "result0047_16.nsv", "result0047_17.nsv", "result0047_18.nsv", "result0047_19.nsv", "result0047_20.nsv", "result0047_21.nsv", "result0047_22.nsv", "result0047_23.nsv", "result0047_24.nsv", "result0047_25.nsv", "result0047_26.nsv", "result0047_27.nsv", "result0047_28.nsv", "result0047_29.nsv", "result0047_30.nsv", "result0047_31.nsv", "result0047_32.nsv", "result0047_33.nsv", "result0047_34.nsv"];
val thyn = "vfmTestDefs0047";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
