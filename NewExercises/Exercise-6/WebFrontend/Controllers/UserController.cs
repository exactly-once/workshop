using Microsoft.AspNetCore.Mvc;
using Orders.Models;

namespace Orders.Controllers
{
    public class UserController : Controller
    {
        [Route("")]
        [Route("user")]
        [HttpGet]
        public IActionResult Index()
        {
            return View();
        }

        [Route("user")]
        [HttpPost]
        public IActionResult LogIn(UserModel user)
        {
            return RedirectToAction("Index", "Orders", new { customerId = user.Name });
        }
    }
}