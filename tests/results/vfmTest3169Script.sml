Theory vfmTest3169[no_sig_docs]
Ancestors vfmTestDefs3169
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result3169_0.nsv", "result3169_1.nsv", "result3169_2.nsv", "result3169_3.nsv", "result3169_4.nsv", "result3169_5.nsv"];
val thyn = "vfmTestDefs3169";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
