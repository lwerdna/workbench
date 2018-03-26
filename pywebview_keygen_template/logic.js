
function clearuser(params) {
	document.getElementById('user').value = ""
	document.getElementById('serial').value = ""
}

function populateSerial(response) {
    console.debug(response)
    console.debug(response.message)
    document.getElementById('serial').value = response.message
}

function generate(params) {
    var user = document.getElementById('user').value
    promise = pywebview.api.generate(user)
    promise.then(populateSerial)
}

